#!/usr/bin/env python3
"""Build both mathematical libraries and audit all their imported declarations.

Run from the repository with:
    lake env python3 scripts/audit_axioms.py --output /tmp/acl_geom_axiom_audit

The output directory must be empty or new. The report records source hashes,
the Git head and whether the tracked tree was clean. Agents must also enforce
the process-family memory limit in AGENTS.md when invoking this command.
"""

from argparse import ArgumentParser
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent.parent
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def command_output(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True)


def source_pins():
    files = command_output("rg", "--files", "AclGeom", "GroupConfig").splitlines()
    files = sorted({p for p in files if p.endswith(".lean")} | {
        "AclGeom.lean", "GroupConfig.lean"})
    return {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in files}


def build_input_pins():
    configs = [p for p in ["lakefile.toml", "lakefile.lean"] if (ROOT / p).is_file()]
    if not configs:
        raise RuntimeError("No Lake configuration file found")
    return {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
            for p in ["lean-toolchain", "lake-manifest.json", *configs]}


def save_json(output, name, value):
    (output / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def run_logged(output, name, args):
    with (output / name).open("w") as log:
        result = subprocess.run(args, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"Command failed ({result.returncode}); see {output / name}")


def audit(output):
    started = time.monotonic()
    head = command_output("git", "rev-parse", "HEAD").strip()
    clean = subprocess.run(["git", "diff", "--quiet", "HEAD"], cwd=ROOT).returncode == 0
    pins = source_pins()
    build_inputs = build_input_pins()
    modules = {p.removesuffix(".lean").replace("/", ".") for p in pins}
    source_digest = hashlib.sha256(json.dumps(pins, sort_keys=True).encode()).hexdigest()
    save_json(output, "source_pins.json", pins)
    save_json(output, "invocation.json", {
        "git_head": head, "tracked_tree_clean": clean,
        "source_digest": source_digest,
        "build_input_sha256": build_inputs,
        "lean_version": command_output("lean", "--version").strip(),
        "auditor_sha256": {
            name: hashlib.sha256((ROOT / "scripts" / name).read_bytes()).hexdigest()
            for name in ["audit_axioms.py", "audit_axioms.lean"]}})

    # A plain Lean import can load stale oleans. Build the roots first so that
    # the declaration report corresponds to the source files whose hashes we save.
    run_logged(output, "build.log", ["lake", "build", "AclGeom", "GroupConfig"])
    run_logged(output, "audit.log", [
        "lean", "-R", str(ROOT), "-DrelaxedAutoImplicit=false",
        "-DmaxSynthPendingDepth=3", "-Dlinter.mathlibStandardSet=true",
        str(ROOT / "scripts/audit_axioms.lean")])
    log = (output / "audit.log").read_text()
    if re.search(r"warning:|error[:(]", log):
        raise RuntimeError(f"Audit emitted diagnostics; see {output / 'audit.log'}")
    imported = set(re.findall(r"^MODULE\|(.+)$", log, re.MULTILINE))
    if imported != modules:
        raise RuntimeError(
            f"Module inventory mismatch: missing={sorted(modules - imported)}, "
            f"unexpected={sorted(imported - modules)}")
    rows = [json.loads(line[5:]) for line in log.splitlines() if line.startswith("DECL|")]
    if not rows or len({row["name"] for row in rows}) != len(rows):
        raise RuntimeError("Empty or duplicate declaration inventory")
    nonstandard = [row for row in rows if not set(row["axioms"]) <= STANDARD_AXIOMS]
    project_axioms = [row for row in rows if row["kind"] == "axiom"]
    public = [row for row in rows if not row["private"]]
    public_theorems = [row for row in public if row["kind"] == "theorem"]
    if (source_pins() != pins or build_input_pins() != build_inputs or
            command_output("git", "rev-parse", "HEAD").strip() != head):
        raise RuntimeError("Source files or Git head changed during the audit")
    report = {
        "git_head": head, "tracked_tree_clean": clean,
        "source_digest": source_digest,
        "project_modules": len(modules), "loaded_project_declarations": len(rows),
        "public_declarations": len(public), "public_theorems": len(public_theorems),
        "private_declarations": len(rows) - len(public),
        "unsafe_declarations": sum(row["unsafe"] for row in rows),
        "unsafe_public_declarations": [row["name"] for row in public if row["unsafe"]],
        "public_kind_counts": dict(sorted(Counter(row["kind"] for row in public).items())),
        "project_axiom_declarations": project_axioms,
        "nonstandard_declarations": nonstandard,
        "standard_axioms": sorted(STANDARD_AXIOMS),
        "green": not nonstandard and not project_axioms,
        "seconds": round(time.monotonic() - started, 2),
        "scope": (
            "All public declarations, including generated declarations, from both "
            "mathematical library roots; the imported module inventory must equal "
            "all mathematical source modules. Selection uses each declaration's "
            "declaring module rather than its namespace. Private declarations "
            "present in the imported environment are also recorded and checked. "
            "This is a dependency audit, not a source-coverage audit.")}
    save_json(output, "declarations.json", rows)
    save_json(output, "summary.json", report)
    print(json.dumps(report, ensure_ascii=False), flush=True)
    if not report["green"]:
        raise RuntimeError("Nonstandard dependencies or project axioms; see summary.json")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True,
                        help="New or empty directory for logs and JSON evidence")
    output = parser.parse_args().output.resolve()
    if output.exists() and (not output.is_dir() or any(output.iterdir())):
        parser.error("--output must be a new or empty directory")
    output.mkdir(parents=True, exist_ok=True)
    try:
        audit(output)
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as error:
        print(json.dumps({"green": False, "reason": str(error), "output": str(output)}),
              file=sys.stderr, flush=True)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

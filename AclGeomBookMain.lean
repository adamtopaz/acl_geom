import VersoManual
import AclGeomBook

open Verso.Genre.Manual

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2

def main := manualMain (%doc AclGeomBook) (config := config)

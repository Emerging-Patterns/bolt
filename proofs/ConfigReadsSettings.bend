# proofs of laws/ConfigReadsSettings.bend
import Base
import ../src/config.bend as Config
import ../laws/ConfigReadsSettings.bend as Laws

def Laws.unquote_strips_quotes(tt, e):
  %Equal.sym(Bool, Bool.and(String.starts_with(tt, "\""), String.ends_with(tt, "\"")), True{}, e) :
    {Bool.pick(String, _, String.take(String.drop(tt, 1n), (String.length(tt) - 2n : Nat)), tt)
      == String.take(String.drop(tt, 1n), (String.length(tt) - 2n : Nat)) : String}
  {==}

def Laws.unquote_keeps_bare(tt, e):
  %Equal.sym(Bool, Bool.and(String.starts_with(tt, "\""), String.ends_with(tt, "\"")), False{}, e) :
    {Bool.pick(String, _, String.take(String.drop(tt, 1n), (String.length(tt) - 2n : Nat)), tt) == tt : String}
  {==}

def Laws.levels_in_order(_n, _w, _line, _rest):
  {==}

def Laws.parse_reads_settings(_text):
  {==}

def Laws.settings_in_file_order(_kids, _body, _rest):
  {==}

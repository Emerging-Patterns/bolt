# proofs of laws/ConfigReadsSettings.bend
import Base
import ../src/config.bend as Config
import ../laws/ConfigReadsSettings.bend as Laws

def Laws.unquote_strips_quotes(t, e):
  %Equal.sym(Bool, Bool.and(String.starts_with(t, "\""), String.ends_with(t, "\"")), True{}, e) :
    {Bool.pick(String, _, String.take(String.drop(t, 1n), (String.length(t) - 2n : Nat)), t)
      == String.take(String.drop(t, 1n), (String.length(t) - 2n : Nat)) : String}
  {==}

def Laws.unquote_keeps_bare(t, e):
  %Equal.sym(Bool, Bool.and(String.starts_with(t, "\""), String.ends_with(t, "\"")), False{}, e) :
    {Bool.pick(String, _, String.take(String.drop(t, 1n), (String.length(t) - 2n : Nat)), t) == t : String}
  {==}

def Laws.levels_in_order(_n, _w, _line, _rest):
  {==}

def Laws.parse_reads_settings(_text):
  {==}

def Laws.settings_in_file_order(_kids, _body, _rest):
  {==}

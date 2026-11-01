# proofs of laws/ConfigUnknownLevelIsError.bend
import Base
import ../src/config.bend as Config
import ../laws/ConfigUnknownLevelIsError.bend as Laws

def Laws.word_error(ww, h_off, h_warn):
  o = Equal.sym(Bool, String.eq(ww, "off"), False{}, h_off)
  %o : {Bool.pick(Config.Level, _, Config.Off{},
      Bool.pick(Config.Level, String.eq(ww, "warn"), Config.Warn{}, Config.Error{}))
    == Config.Error{} : Config.Level}
  w = Equal.sym(Bool, String.eq(ww, "warn"), False{}, h_warn)
  %w : {Bool.pick(Config.Level, _, Config.Warn{}, Config.Error{}) == Config.Error{} : Config.Level}
  {==}

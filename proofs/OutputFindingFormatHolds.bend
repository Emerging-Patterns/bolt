# proofs of laws/OutputFindingFormatHolds.bend
import Base
import ../src/config.bend as Config
import ../laws/OutputFindingFormatHolds.bend as Laws

def Laws.level_words(ll):
  match ll:
    case Config.Off{}:
      {==}
    case Config.Warn{}:
      {==}
    case Config.Error{}:
      {==}

def Laws.shown(_path, _line, _col, _len, _rule, _msg, _level):
  {==}

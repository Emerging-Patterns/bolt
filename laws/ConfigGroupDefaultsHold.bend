# Group defaults are correctness at error, pedantic off, and the rest at warn.
import Base
import ../src/config.bend as Config

# LAW: correctness defaults to error
law default_correctness:
  for +group: String
  for h: {group == "correctness" : String}
  {Config.default(group) == Config.Error{} : Config.Level}

# LAW: pedantic defaults to off
law default_pedantic:
  for +group: String
  for h: {group == "pedantic" : String}
  {Config.default(group) == Config.Off{} : Config.Level}

# LAW: every other group defaults to warn
law default_rest:
  for +group: String
  for h_c: {String.eq(group, "correctness") == False{} : Bool}
  for h_p: {String.eq(group, "pedantic") == False{} : Bool}
  {Config.default(group) == Config.Warn{} : Config.Level}

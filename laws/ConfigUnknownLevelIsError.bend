# A level word that is not `off` or `warn` grades as error.
import Base
import ../src/config.bend as Config

# LAW: a level word that is neither `off` nor `warn` is an error, so a typo
# makes a rule stricter, never silently off
law word_error:
  for +ww: String
  for h_off: {String.eq(ww, "off") == False{} : Bool}
  for h_warn: {String.eq(ww, "warn") == False{} : Bool}
  {Config.of_word(ww) == Config.Error{} : Config.Level}

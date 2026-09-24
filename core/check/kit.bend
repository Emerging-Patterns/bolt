# check/kit: a tiny test kit. Its Reporter is an injected effect service, so
# the kit's own output is swappable -- core dogfoods itself here.
import Base
import ./service.bend as S

# passes when two strings are equal
def eq_str(~rep: S.Reporter, name: String, got: String, want: String) -> IO(Unit):
  S.report(String.eq(got, want), rep, name)

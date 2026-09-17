# check/kit: a tiny test kit. Its Reporter is an injected effect service, so
# the kit's own output is swappable -- wire dogfoods itself here.
import Base
import ./service.bend as S

def eq_u32(~rep: S.Reporter, name: String, got: U32, want: U32) -> IO(Unit):
  S.report(U32.is_eq(got, want), rep, name)

def eq_str(~rep: S.Reporter, name: String, got: String, want: String) -> IO(Unit):
  S.report(String.eq(got, want), rep, name)

# lsp/frame: Content-Length framing over bytes, and UTF-8 both ways
import Base
import ../frame.bend as Frame
import ../../../core/check/kit.bend as Check
import ../../../core/check/print.bend as Report

# what a cut found: the body and how many bytes are left, or "more"
def show(c: Frame.Cut) -> String:
  match c:
    case Frame.More{}:
      "more"
    case Frame.Ready{body, rest}:
      Frame.decode(body) ++ " +" ++ Nat.show(List.length(&2, U32, rest))

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str(~Report.new(), "wrap counts bytes", Frame.wrap("{}"), "Content-Length: 2\r\n\r\n{}")
    Check.eq_str(~Report.new(), "wrap counts UTF-8 bytes, not chars", Frame.wrap("é€😀"), "Content-Length: 9\r\n\r\né€😀")
    Check.eq_str(~Report.new(), "UTF-8 round-trips", Frame.decode(Frame.encode("aé€😀z")), "aé€😀z")
    Check.eq_str(~Report.new(), "a whole message cuts", show(Frame.cut(Frame.encode(Frame.wrap("{\"a\":1}") ++ "Cont"))), "{\"a\":1} +4")
    Check.eq_str(~Report.new(), "other headers are skipped", show(Frame.cut(Frame.encode("Content-Type: x; charset=utf-8\r\nContent-Length: 2\r\n\r\n[]"))), "[] +0")
    Check.eq_str(~Report.new(), "a partial header waits", show(Frame.cut(Frame.encode("Content-Length: 12\r\n"))), "more")
    Check.eq_str(~Report.new(), "a partial body waits", show(Frame.cut(Frame.encode("Content-Length: 12\r\n\r\n{\"a\":"))), "more")
    Check.eq_str(~Report.new(), "a multi-byte body cuts by bytes", show(Frame.cut(Frame.encode(Frame.wrap("\"é\"") ++ "x"))), "\"é\" +1")

#|ok wrap counts bytes
#|ok wrap counts UTF-8 bytes, not chars
#|ok UTF-8 round-trips
#|ok a whole message cuts
#|ok other headers are skipped
#|ok a partial header waits
#|ok a partial body waits
#|ok a multi-byte body cuts by bytes

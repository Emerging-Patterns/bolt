# bench: project-rule timing over many files (not part of bolt).
# project.bend <path>...
import Base
import ../../bolt/args.bend as Args
import ../../bolt/src.bend as Src
import ../../bolt/finding.bend as F
import ../../bolt/lsp/files/disk.bend as Disk
import ../../bolt/rules/digest.bend as Digest
import ../../bolt/rules/laws/law.bend as Law
import ../../bolt/rules/laws/unsafe.bend as Unsafe
import ../../bolt/rules/laws/trace.bend as Trace
import ../../bolt/noqa.bend as Noqa

# a count on stderr
def say(+name: String, +n: U32) -> IO(Unit):
  IO.print_err(name ++ " " ++ U32.show(n))

def load.one(mm: Maybe<&2, String>, +p: String, more: List<&2, Src.Src>) -> List<&2, Src.Src>:
  match mm:
    case None{}:
      more
    case Some{+text}:
      Src.of(p, text) <> more

# each file read and parsed
def load(ps: List<&2, String>) -> IO(List<&2, Src.Src>):
  match ps:
    case Nil{}:
      IO.pure(List<&2, Src.Src>, [])
    case Con{+p, rest}:
      do IO<List<&2, Src.Src>>:
        mm : Maybe<&2, String> <- Disk.read(p)
        more : List<&2, Src.Src> <- load(rest)
        return load.one(mm, p, more)

# the project rules, one at a time
def go(+ss: List<&2, Src.Src>) -> IO(Unit):
  +ds = Digest.all(ss)
  do IO<Unit>:
    say("srcs", U32.from_nat(List.length(&2, Src.Src, ss)))
    say("digest", U32.from_nat(List.length(&2, Digest.Digest, ds)))
    say("coverage", U32.from_nat(List.length(&2, F.Finding, Law.check(ds))))
    say("unsafe", U32.from_nat(List.length(&2, F.Finding, Unsafe.check(ds))))
    say("trace", U32.from_nat(List.length(&2, F.Finding, Trace.check(True{}, None{}, ds))))
    say("noqa.marks", U32.from_nat(List.length(&2, Noqa.Marks, Noqa.of_srcs(ss))))

def main() -> IO(Unit):
  do IO<Unit>:
    av : List<&2, String> <- Args.argv()
    ss : List<&2, Src.Src> <- load(av)
    go(ss)

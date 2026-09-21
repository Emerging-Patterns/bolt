# the packaged build (flake.nix). `nix flake check` builds `checks.bolt` --
# bend emits the C and compiles it, the way a `nix profile install` does.
# That is not anything the two lanes of `ez test` answer: they say the source
# checks and runs, not that the thing people install still builds.
#
# nix sees tracked files only, so a change has to be `git add`ed before this
# says anything about it.
#
# The old gate grepped this run's output for the word "error". The status is
# the stronger reading of the same thing: `nix flake check` exits non-zero when
# any check fails. This is also the one job nothing here can cap: with a
# nix-daemon running, the build happens in nix-daemon.service and not in any
# cgroup a test could make. Capping it is a MemoryMax drop-in on
# nix-daemon.service, not a change this repo can make.
import Base
import 0x29fbb19f01e963cc6271864b7e442159/main.bend as Snap
import ../core/check/kit.bend as Check
import ../core/check/print.bend as Report

def main() -> IO(Unit):
  do IO<Unit>:
    checked : String <- Snap.exec(["nix", "flake", "check"])
    Check.eq_str(~Report.new(), "nix flake check: the package and its C toolchain build",
      Snap.code(checked), "0")

#|ok nix flake check: the package and its C toolchain build

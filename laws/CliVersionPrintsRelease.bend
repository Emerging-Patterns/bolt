# `--version` prints the release and, when the build has one, the short commit
# in parentheses.
#
# also rests on: laws/CliVersion.bend, laws/CliVersionExits.bend
import Base
import ../src/args.bend as Args

# LAW: a build with no commit prints the release alone
law version_release:
  for +rel: String
  for +rev: String
  for h: {String.is_empty(rev) == True{} : Bool}
  {Args.version.at(rel, rev) == rel : String}

# LAW: a build with a commit prints the release, then the commit in
# parentheses
law version_commit:
  for +rel: String
  for +rev: String
  for h: {String.is_empty(rev) == False{} : Bool}
  {Args.version.at(rel, rev) == rel ++ " (" ++ rev ++ ")" : String}

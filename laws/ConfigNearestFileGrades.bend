# A finding is graded by the nearest readable bolt.bend in its file's
# directory, then each parent, and only that one applies.
import Base
import ../src/config.bend as Config
import ../src/rules/laws/law.bend as Law
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan

# Where a finding is graded (laws/ConfigNearestFileGrades.bend). The planner grades a finding by the
# config of its path's directory (plan.bend, config.at), from a table it builds
# once for each directory in the run. The laws below say what that config is,
# for every World and every path: the path's directory is resolved against
# the World's working directory (Config.home: absolute, then home.step over
# each segment), and of it and each parent up to the root (Config.chain),
# nearest first, the first whose bolt.bend the World holds a text for grades
# the finding.

# LAW: a path that starts at the root is itself, wherever bolt runs from
law absolute_root:
  for +cwd: String
  for +path: String
  for h: {String.starts_with(path, "/") == True{} : Bool}
  {Config.absolute(cwd, path) == path : String}

# LAW: any other path is read under the working directory
law absolute_under:
  for +cwd: String
  for +path: String
  for h: {String.starts_with(path, "/") == False{} : Bool}
  {Config.absolute(cwd, path) == cwd ++ "/" ++ path : String}

# LAW: an empty segment (from `//`, or the `/` a directory ends in) leaves the
# directory where it is
law home_empty:
  for +above: List<&2, String>
  {Config.home.step("", above) == above : List<&2, String>}

# LAW: a `.` segment leaves the directory where it is
law home_here:
  for +above: List<&2, String>
  {Config.home.step(".", above) == above : List<&2, String>}

# LAW: a `..` segment goes up one directory: it drops the innermost one, and
# at the root there is none to drop (home.up)
law home_up:
  for +above: List<&2, String>
  {Config.home.step("..", above) == Config.home.up(above) : List<&2, String>}

# LAW: any other segment goes into the directory it names
law home_down:
  for +seg: String
  for +above: List<&2, String>
  for h_here: {Bool.or(String.is_empty(seg), String.eq(seg, ".")) == False{} : Bool}
  for h_up: {String.eq(seg, "..") == False{} : Bool}
  {Config.home.step(seg, above) == seg <> above : List<&2, String>}

# LAW: a resolved directory's candidates are its own bolt.bend, then its
# parent's candidates, so they reach every parent up to the root
law chain_parent:
  for +d: String
  for +rest: List<&2, String>
  {Config.chain(d <> rest) == (Config.root(d <> rest, "") ++ "bolt.bend") <> Config.chain(rest)
    : List<&2, String>}

# LAW: the outermost directory's candidates are its own bolt.bend, then the
# root's, `/bolt.bend`, and no more
law chain_ends_at_root:
  for +d: String
  {Config.chain([d]) == ["/" ++ (d ++ "/") ++ "bolt.bend", "/bolt.bend"] : List<&2, String>}

# LAW: a directory's path runs from the root, each directory then a `/`
law root_from_the_top:
  for +d: String
  for +acc: String
  {Config.root([d], acc) == "/" ++ d ++ "/" ++ acc : String}

# the config a World's answer for a candidate gives: its text parsed when it
# was read, else what the candidates after it give. Law vocabulary, as is
# first_read.
def first_read.at(m: Maybe<&2, W.Answer>, more: Config.Config) -> Config.Config:
  match m:
    case None{}:
      more
    case Some{W.Listed{_names}}:
      more
    case Some{W.Read{text}}:
      Config.parse(text)
    case Some{W.Unread{}}:
      more
    case Some{W.Directory{}}:
      more

# the config of the first of the paths the World read a text for, the
# defaults when it read none of them
def first_read(+world: W.World, ps: List<&2, String>) -> Config.Config:
  match ps:
    case Nil{}:
      Config.none()
    case Con{p, rest}:
      first_read.at(W.answer(world, W.Contents{p}), first_read(world, rest))

# LAW: a finding at a path is graded by the nearest bolt.bend the World read:
# of the bolt.bend in the path's directory, resolved against the working
# directory, then in each parent up to the root, the first read, and only
# that one; the defaults when none was
law nearest_grades:
  for +world: W.World
  for +path: String
  {Plan.config.at(Plan.confs(world), world, path)
    == first_read(world, Config.chain(Config.home(W.cwd.of(world), Config.dir_of(path))))
    : Config.Config}

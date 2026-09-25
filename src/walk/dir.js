// walkdir.entries: the JS lane's twin of dir.c: the names directly in a
// directory, one a line, a directory's name ending in "/"; a directory that
// cannot be read answers nothing. A symbolic link is named as a file, even
// when it points at a directory, so a link cannot make the walk loop.
function walkdir_entries(dir) {
  const fs = require("fs");
  let entries;
  try {
    entries = fs.readdirSync(dir, { withFileTypes: true });
  } catch (e) {
    return "";
  }
  return entries.map((e) => e.name + (e.isDirectory() ? "/" : "") + "\n").join("");
}

io_eff(CID(walkdir.entries), walkdir_entries);

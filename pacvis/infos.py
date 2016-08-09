from itertools import groupby

import pyalpm
import pycman

from .console import start_message, append_message, print_message

class DbInfo:
    def __init__(self):
        self.handle = pycman.config.init_with_config("/etc/pacman.conf")
        self.localdb = self.handle.get_localdb()
        self.syncdbs = self.handle.get_syncdbs()
        self.packages = self.localdb.pkgcache
        self.all_pkgs = {}
        self.groups = {}

    def find_syncdb(self, pkgname):
        repos = dict((db.name,db) for db in self.syncdbs)
        found, pkg = pycman.action_sync.find_sync_package(pkgname, repos)
        if found:
            return pkg.db.name
        return self.localdb.name

    def get(self, pkgname):
        return self.all_pkgs[pkgname]

    def resolve_dependency(self, dep):
        pkg = self.localdb.get_pkg(dep)
        if pkg is None:
            pkg = pyalpm.find_satisfier(self.packages, dep)
        return pkg

    def find_all(self):
        for pkg in self.packages:
            PkgInfo(pkg.name, self)
        return self.all_pkgs

    def find_circles(self):
        """ https://zh.wikipedia.org/wiki/Tarjan%E7%AE%97%E6%B3%95 """
        stack = list()
        indexes = dict()
        lowlinks = dict()
        index = 0

        def strongconnect(pkg):
            nonlocal stack, indexes, lowlinks, index
            indexes[pkg] = index
            lowlinks[pkg] = index
            index += 1
            stack.append(pkg)
            for dep in self.get(pkg).deps:
                if dep not in indexes:
                    strongconnect(dep)
                    lowlinks[pkg] = min(lowlinks[pkg], lowlinks[dep])
                elif dep in stack:
                    lowlinks[pkg] = min(lowlinks[pkg], indexes[dep])
            if lowlinks[pkg] == indexes[pkg]:
                cirdeps = []
                while True:
                    w = stack.pop()
                    cirdeps.append(w)
                    if (w == pkg):
                        break
                self.get(pkg).circledeps = cirdeps

        for pkg in self.all_pkgs:
            if pkg not in indexes:
                strongconnect(pkg)

    def top_down_sort(self, usemagic):
        remain_pkgs = {x for x in self.all_pkgs}
        start_message("Sorting ")
        while len(remain_pkgs) > 0:
            pkg = remain_pkgs.pop()
            origin_level = self.get(pkg).level
            append_message("%s %d (remaining %d)" % (pkg,
                                                     origin_level,
                                                     len(remain_pkgs)))
            if len(self.get(pkg).deps) == 0:
                if len(self.get(pkg).requiredby) == 0:
                    self.get(pkg).level = 0
                continue
            max_level = max(self.get(x).level for x in self.get(pkg).deps) + 1
            if usemagic:
                # below is magic
                new_level = max_level + int(math.log(1 +
                                                     len(self.get(pkg).deps) +
                                                     len(self.get(pkg).requiredby)))
            else:
                new_level = max_level  # we may not need magic at all
            if new_level != origin_level:
                self.get(pkg).level = new_level
                remain_pkgs.update(set(self.get(pkg).requiredby)
                                   .difference(self.get(pkg).circledeps))

    def buttom_up_sort(self):
        remain_pkgs = {x for x in self.all_pkgs}
        start_message("Resorting ")
        while len(remain_pkgs) > 0:
            pkg = remain_pkgs.pop()
            origin_level = self.get(pkg).level
            append_message("%s %d (remaining %d)" % (pkg,
                                                     origin_level,
                                                     len(remain_pkgs)))
            if len(self.get(pkg).requiredby) == 0:
                if len(self.get(pkg).deps) == 0:
                    self.get(pkg).level = 0
                continue
            min_level = min(self.get(x).level for x in self.get(pkg).requiredby)
            new_level = min_level - 1
            if new_level > origin_level:
                self.get(pkg).level = new_level
                remain_pkgs.update(set(self.get(pkg).deps)
                                   .difference(self.get(pkg).circledeps))

    def minimize_levels(self):
        start_message("Minimizing levels ... ")
        pkgs = list(sorted(self.all_pkgs.values(), key=lambda x: x.level))
        nextlevel = 0
        for key, group in groupby(pkgs, key=lambda x: x.level):
            for pkg in group:
                pkg.level = nextlevel
            nextlevel += 1
        append_message("max available level: %d" % nextlevel)

    def topology_sort(self, usemagic, aligntop):
        self.top_down_sort(usemagic)
        self.buttom_up_sort()
        if aligntop:
            self.top_down_sort(usemagic) # do top_down_sort again to align to top
        self.minimize_levels()

    def calcCSize(self, pkg):
        removing_pkg = set()

        def remove_pkg(pkgname):
            nonlocal removing_pkg
            removing_pkg.add(pkgname)
            for dep in self.get(pkgname).requiredby:
                if dep not in removing_pkg:
                    remove_pkg(dep)

        remove_pkg(pkg.name)
        pkg.csize = sum(self.get(pkg).isize for pkg in removing_pkg)
        append_message("csize %s: %d" % (pkg.name, pkg.csize))
        return pkg.csize

    def calcCsSize(self, pkg):
        removing_pkg = set()
        analyzing_pkg = set()

        def remove_pkg(pkgname):
            nonlocal removing_pkg
            removing_pkg.add(pkgname)
            for dep in self.get(pkgname).deps:
                if not self.get(dep).explicit:
                    analyzing_pkg.add(dep)
            for dep in self.get(pkgname).requiredby:
                if dep not in removing_pkg:
                    remove_pkg(dep)

        remove_pkg(pkg.name)
        while len(analyzing_pkg) > 0:
            apkg = self.get(analyzing_pkg.pop())
            if apkg.name in removing_pkg:
                continue
            if all(dep in removing_pkg for dep in apkg.requiredby):
                remove_pkg(apkg.name)
        pkg.cssize = sum(self.get(pkg).isize for pkg in removing_pkg)
        append_message("cssize %s: %d" % (pkg.name, pkg.cssize))
        return pkg.cssize

    def calcSizes(self):
        start_message("Calculating csize ... ")
        maxCSize = max(self.calcCSize(pkg) for pkg in self.all_pkgs.values())
        append_message(" max cSize: " + str(maxCSize))
        start_message("Calculating cssize ... ")
        maxCsSize = max(self.calcCsSize(pkg) for pkg in self.all_pkgs.values())
        append_message(" max csSize: " + str(maxCsSize))


class PkgInfo:

    def __init__(self, name, dbinfo):
        self.name = name
        self.pkg = dbinfo.localdb.get_pkg(name)
        self.deps = [dbinfo.resolve_dependency(dep).name
                     for dep in self.pkg.depends]
        self.requiredby = self.pkg.compute_requiredby()
        self.optdeps = []
        for dep in self.pkg.optdepends:
            depname = dep.split(":")[0]
            resolved = dbinfo.resolve_dependency(depname)
            if resolved is not None:
                self.optdeps.append(resolved.name)
        self.level = 1
        self.circledeps = []
        self.explicit = self.pkg.reason == 0
        self.isize = self.pkg.isize
        self.desc = self.pkg.desc
        self.version = self.pkg.version
        self.repo = dbinfo.find_syncdb(self.name)
        dbinfo.all_pkgs[name] = self
        self.groups = self.pkg.groups
        for grp in self.groups:
            if grp in dbinfo.groups:
                dbinfo.groups[grp].add_pkg(self.name)
            else:
                GroupInfo(grp, dbinfo)
                dbinfo.groups[grp].add_pkg(self.name)


class GroupInfo (PkgInfo):
    def __init__(self, name, dbinfo):
        self.name = name
        self.deps = []
        self.requiredby = []
        self.optdeps = []
        self.level = 1
        self.circledeps = []
        self.groups = []
        self.explicit = True
        self.isize = 0
        self.desc = name + " package group"
        self.version = ""
        self.repo = ""
        self.dbinfo = dbinfo
        self.dbinfo.groups[name] = self
        self.dbinfo.all_pkgs[name] = self

    def add_pkg(self, pkgname):
        self.deps.append(pkgname)
        self.dbinfo.get(pkgname).requiredby.append(self.name)


def test_circle_detection():
    dbinfo = DbInfo()
    start_message("find all packages...")
    dbinfo.find_all()
    append_message("done")
    start_message("find all dependency circles...")
    dbinfo.find_circles()
    append_message("done")
    for name, pkg in dbinfo.all_pkgs.items():
        if len(pkg.circledeps) > 1:
            print_message("%s(%s): %s" %
                          (pkg.name, pkg.circledeps, ", ".join(pkg.deps)))
    dbinfo.topology_sort()
    for pkg in sorted(dbinfo.all_pkgs.values(), key=lambda x: x.level):
        print("%s(%d): %s" % (pkg.name, pkg.level, ", ".join(pkg.deps)))
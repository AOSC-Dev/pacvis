from itertools import groupby
import math
import re
import collections
import sqlite3
import operator

from distutils.version import LooseVersion

from .console import start_message, append_message, print_message

SQL_GET_ALL_PKGS = """
SELECT
  name,
  (category || '-' || section) AS section,
  CASE
    WHEN release IS NULL THEN version
    ELSE (version || '-' || release)
  END AS version,
  base.groups,
  dep.provides,
  dep.depends,
  dep.optdepends,
  description AS desc
FROM packages
LEFT JOIN (
    SELECT
      package,
      group_concat(
        CASE WHEN relationship = 'PKGREP' AND version = ''
        THEN dependency END
      ) provides,
      group_concat(CASE WHEN relationship = 'PKGDEP' THEN dependency END) depends,
      group_concat(CASE WHEN relationship = 'PKGRECOM' THEN dependency END) optdepends
    FROM package_dependencies
    GROUP BY package
  ) dep
  ON dep.package = packages.name
LEFT JOIN (
    SELECT
      pkgdep.dependency package,
      group_concat(pkgdep.package) groups
    FROM package_dependencies pkgdep
    LEFT JOIN packages ON pkgdep.package = packages.name
    WHERE packages.section = 'bases' AND pkgdep.relationship = 'PKGDEP'
    GROUP BY dependency
  ) base
  ON base.package = packages.name
WHERE packages.section != 'bases'
"""

RE_dep = re.compile(r'^([a-z0-9][a-z0-9+.-]*)(.*)$')
RE_comp = re.compile(r'([<>]=|<<|>>|[<=>])')
DEP_OPERATORS = {
    '<<': operator.lt,
    '<': operator.le,
    '<=': operator.le,
    '=': operator.eq,
    '>=': operator.ge,
    '>': operator.ge,
    '>>': operator.gt
}

Package = collections.namedtuple('Package', (
    'name', 'section', 'version', 'groups',
    'provides', 'depends', 'optdepends', 'desc'
))

class AbbsDB:
    def __init__(self, db):
        self.name = db
        self.packages = []
        self.package_dict = {}
        self.load()

    def load(self):
        conn = sqlite3.connect(self.name)
        cur = conn.cursor()
        for row in cur.execute(SQL_GET_ALL_PKGS):
            name, section, version, groups, provides, depends, optdepends, desc = row
            pkg = Package(
                name, section, version,
                groups.split(',') if groups else [],
                provides.split(',') if provides else [],
                depends.split(',') if depends else [],
                optdepends.split(',') if optdepends else [],
                desc
            )
            self.packages.append(pkg)
            self.package_dict[name] = pkg
        conn.close()

    def find_satisfier(self, dep):
        deppkgname, depcomp = RE_dep.match(dep).groups()
        if depcomp:
            depverop = RE_comp.match(s).group(0)
            depver = depcomp[len(depverop):]
        deppkg = self.package_dict.get(deppkgname)
        if deppkg and (not depcomp or DEP_OPERATORS[depverop](
            LooseVersion(deppkg.version), LooseVersion(depver))):
            return deppkg
        for pkg in self.packages:
            if deppkgname in pkg.provides and not depcomp:
                return pkg

class DbInfo:
    def __init__(self, db='abbs.db'):
        self.localdb = AbbsDB(db)
        self.packages = self.localdb.packages
        self.all_pkgs = {}
        self.groups = {}
        self.vdeps = {}
        self.repo = RepoInfo(db, self)
        print_message("Loading %s" % db)

    def find_syncdb(self, pkgname):
        repo = self.localdb.name
        self.repo.add_pkg(pkgname)
        return repo

    def get(self, pkgname):
        return self.all_pkgs[pkgname]

    def resolve_dependency(self, dep):
        if dep in self.all_pkgs:
            return dep
        pkg = self.localdb.find_satisfier(dep)
        if pkg is None:
            return None
        return pkg.name

    def find_all(self, showallvdeps):
        for pkg in self.packages:
            PkgInfo(pkg.name, self)
        for pkg in self.all_pkgs.values():
            pkg.find_dependencies(self)
        if showallvdeps:
            return self.all_pkgs
        # remove vdeps without requiredby
        for pkg in list(self.all_pkgs.values()):
            if type(pkg) is VDepInfo:
                if len(pkg.requiredby) == 0:
                    for dep in pkg.deps:
                        while pkg.name in self.get(dep).requiredby:
                            self.get(dep).requiredby.remove(pkg.name)
                    self.repo.pkgs.remove(pkg.name)
                    del self.all_pkgs[pkg.name]
                    del self.vdeps[pkg.name]
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

    def top_down_sort(self, usemagic, all_pkgs):
        remain_pkgs = set(all_pkgs)
        start_message("Top-down sorting ")
        while len(remain_pkgs) > 0:
            pkg = remain_pkgs.pop()
            pkginfo = self.get(pkg)
            origin_level = pkginfo.level
            append_message("%s %d (remaining %d)" % (pkg,
                                                     origin_level,
                                                     len(remain_pkgs)))
            if len(all_pkgs.intersection(pkginfo.deps)) == 0:
                if all([len(pkginfo.deps) == 0,
                        len(pkginfo.requiredby) == 0]):
                    pkginfo.level = 0
                continue
            max_level = 1 + max(self.get(x).level
                                for x in all_pkgs.intersection(pkginfo.deps))
            if usemagic:
                # below is magic
                new_level = max_level + int(math.log(1 +
                                                     len(pkginfo.deps) +
                                                     len(pkginfo.requiredby)))
            else:
                new_level = max_level  # we may not need magic at all
            if new_level != origin_level:
                pkginfo.level = new_level
                remain_pkgs.update(
                    all_pkgs.intersection(
                        set(pkginfo.requiredby).difference(
                            pkginfo.circledeps)))

    def buttom_up_sort(self, all_pkgs):
        remain_pkgs = set(all_pkgs)
        start_message("Buttom-up sorting ")
        while len(remain_pkgs) > 0:
            pkg = remain_pkgs.pop()
            pkginfo = self.get(pkg)
            origin_level = pkginfo.level
            append_message("%s %d (remaining %d)" % (pkg,
                                                     origin_level,
                                                     len(remain_pkgs)))
            if len(all_pkgs.intersection(pkginfo.requiredby)) == 0:
                continue
            min_level = min(self.get(x).level
                            for x in all_pkgs.intersection(pkginfo.requiredby))
            new_level = min_level - 1
            if new_level > origin_level:
                pkginfo.level = new_level
                remain_pkgs.update(all_pkgs.intersection(set(pkginfo.deps)
                                   .difference(pkginfo.circledeps)))

    def minimize_levels(self, all_pkgs, nextlevel):
        start_message("Minimizing levels ... ")
        pkgs = list(sorted((self.get(pkg) for pkg in all_pkgs),
                           key=lambda x: x.level))
        for key, group in groupby(pkgs, key=lambda x: x.level):
            for pkg in group:
                pkg.level = nextlevel
            nextlevel += 1
        append_message("max available level: %d" % nextlevel)
        return nextlevel

    def topology_sort(self, usemagic, aligntop, mergerepos=True):
        all_pkgs = {x for x in self.all_pkgs}
        self.top_down_sort(usemagic, all_pkgs)
        self.buttom_up_sort(all_pkgs)
        if aligntop:
            # do top_down_sort again to align to top
            self.top_down_sort(usemagic, all_pkgs)
        self.minimize_levels(all_pkgs, 1)

    def calcCSize(self, pkg):
        # really don't know
        pkg.csize = 1
        return pkg.csize

    def calcCsSize(self, pkg):
        # really don't know either
        pkg.cssize = 1
        return pkg.cssize

    def calcSizes(self):
        # start_message("Calculating csize ... ")
        maxCSize = max(self.calcCSize(pkg) for pkg in self.all_pkgs.values())
        # append_message(" max cSize: " + str(maxCSize))
        # start_message("Calculating cssize ... ")
        maxCsSize = max(self.calcCsSize(pkg) for pkg in self.all_pkgs.values())
        # append_message(" max csSize: " + str(maxCsSize))

    def requirement2pkgname(self, requirement):
        if any(x in requirement for x in "<=>"):
            return RE_comp.split(requirement)[0]
        return requirement

    def find_vdep(self, provide, pkg):
        name = self.requirement2pkgname(provide)
        if name in self.all_pkgs:
            return name
        if name not in self.vdeps:
            VDepInfo(name, self)
        self.vdeps[name].deps.append(pkg)
        self.all_pkgs[pkg].requiredby.append(name)
        return name


class PkgInfo:
    def __init__(self, name, dbinfo):
        self.name = name
        self.pkg = dbinfo.localdb.package_dict[name]
        dbinfo.all_pkgs[name] = self
        self.deps = []
        self.requiredby = []
        self.optdeps = []
        self.level = 1
        self.circledeps = []
        self.explicit = 0  # REMOVE
        self.isize = 1 # unknown
        self.desc = self.pkg.desc
        self.version = self.pkg.version
        self.repo = dbinfo.find_syncdb(self.name)
        self.section = self.pkg.section
        self.groups = self.pkg.groups
        self.provides = [dbinfo.find_vdep(pro, self.name)
                         for pro in self.pkg.provides]
        for grp in self.groups:
            if grp in dbinfo.groups:
                dbinfo.groups[grp].add_pkg(self.name)
            else:
                GroupInfo(grp, dbinfo)
                dbinfo.groups[grp].add_pkg(self.name)

    def find_dependencies(self, dbinfo):
        for dep in self.pkg.depends:
            dependency = dbinfo.resolve_dependency(dep)
            if dependency in dbinfo.all_pkgs:
                self.deps.append(dependency)
                dbinfo.get(dependency).requiredby.append(self.name)
        for dep in self.pkg.optdepends:
            resolved = dbinfo.resolve_dependency(dep)
            if resolved is not None:
                self.optdeps.append(resolved)
        # self.requiredby.extend(self.pkg.compute_requiredby())


class GroupInfo (PkgInfo):
    def __init__(self, name, dbinfo):
        self.name = name
        self.deps = []
        self.requiredby = []
        self.optdeps = []
        self.provides = []
        self.level = 1
        self.circledeps = []
        self.groups = []
        self.explicit = True
        self.isize = 0
        self.desc = name + " package group"
        self.version = ""
        self.repo = None
        self.dbinfo = dbinfo
        self.dbinfo.groups[name] = self
        self.dbinfo.all_pkgs[name] = self

    def add_pkg(self, pkgname):
        self.deps.append(pkgname)
        self.dbinfo.get(pkgname).requiredby.append(self.name)

    def reset_repo(self):
        for pkg in self.deps:
            self.dbinfo.repo.pkgs.add(self.name)
            return

    def find_dependencies(self, dbinfo):
        self.reset_repo()


class VDepInfo (PkgInfo):
    def __init__(self, name, dbinfo):
        self.name = name
        self.deps = []
        self.requiredby = []
        self.optdeps = []
        self.provides = []
        self.level = 1
        self.circledeps = []
        self.groups = []
        self.explicit = True
        self.isize = 0
        self.desc = name + " virtual dependency"
        self.version = ""
        self.repo = None
        self.dbinfo = dbinfo
        self.dbinfo.all_pkgs[name] = self
        self.dbinfo.vdeps[name] = self

    def reset_repo(self):
        for pkg in self.deps:
            self.dbinfo.repo.pkgs.add(self.name)
            return

    def find_dependencies(self, dbinfo):
        self.reset_repo()
        for dep in self.deps:
            dbinfo.get(dep).requiredby.append(self.name)


class RepoInfo:
    def __init__(self, name, dbinfo):
        self.name = name
        self.pkgs = set()
        self.level = -1
        self.dbinfo = dbinfo

    def add_pkg(self, pkgname):
        self.pkgs.add(pkgname)


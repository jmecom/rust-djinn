//! Filesystem operations anchored to open directory descriptors. Every component
//! is opened with O_NOFOLLOW, and writes replace directory entries instead of
//! truncating or changing permissions through an agent-controlled path.

use std::ffi::{CStr, CString, OsStr, OsString};
use std::fs::File;
use std::io::{self, Read, Write};
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::fs::PermissionsExt;
use std::path::{Component, Path};
use std::sync::atomic::{AtomicU64, Ordering};

pub(super) struct Dir(File);

fn cstr(s: &OsStr) -> io::Result<CString> {
    CString::new(s.as_bytes())
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "NUL in path"))
}

fn cvt(n: libc::c_int) -> io::Result<libc::c_int> {
    if n < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(n)
    }
}

fn unique() -> OsString {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    format!(
        ".djinn-tmp-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )
    .into()
}

impl Dir {
    pub(super) fn create_dir(&self, path: &Path) -> io::Result<()> {
        let (parent, name) = self.parent(path, true)?;
        let name = cstr(&name)?;
        cvt(unsafe { libc::mkdirat(parent.0.as_raw_fd(), name.as_ptr(), 0o700) }).map(|_| ())
    }

    pub(super) fn symlink(&self, target: &Path, path: &Path) -> io::Result<()> {
        let (parent, name) = self.parent(path, true)?;
        let name = cstr(&name)?;
        let target = cstr(target.as_os_str())?;
        cvt(unsafe { libc::symlinkat(target.as_ptr(), parent.0.as_raw_fd(), name.as_ptr()) })
            .map(|_| ())
    }

    pub(super) fn open(path: &Path) -> io::Result<Self> {
        let path = path.strip_prefix("/").map_err(|_| {
            io::Error::new(io::ErrorKind::InvalidInput, "directory root must be absolute")
        })?;
        Self(File::open("/")?).subdir(path, false)
    }

    fn child(&self, name: &OsStr, create: bool) -> io::Result<Self> {
        let name = cstr(name)?;
        if create {
            let rc = unsafe { libc::mkdirat(self.0.as_raw_fd(), name.as_ptr(), 0o755) };
            if rc < 0 && io::Error::last_os_error().kind() != io::ErrorKind::AlreadyExists {
                return Err(io::Error::last_os_error());
            }
        }
        let fd = cvt(unsafe {
            libc::openat(
                self.0.as_raw_fd(),
                name.as_ptr(),
                libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            )
        })?;
        Ok(Self(unsafe { File::from_raw_fd(fd) }))
    }

    pub(super) fn subdir(&self, path: &Path, create: bool) -> io::Result<Self> {
        let mut dir = Self(self.0.try_clone()?);
        for component in path.components() {
            let Component::Normal(name) = component else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "path must stay beneath its directory",
                ));
            };
            dir = dir.child(name, create)?;
        }
        Ok(dir)
    }

    fn parent(&self, path: &Path, create: bool) -> io::Result<(Self, OsString)> {
        let name = path
            .file_name()
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "empty filename"))?;
        crate::config::validate_relative_path(path, "mirrored path")
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidInput, e))?;
        Ok((
            self.subdir(path.parent().unwrap(), create)?,
            name.to_owned(),
        ))
    }

    fn read_file(&self, name: &OsStr) -> io::Result<File> {
        let name = cstr(name)?;
        // O_NONBLOCK prevents a substituted FIFO from hanging the verifier.
        let fd = cvt(unsafe {
            libc::openat(
                self.0.as_raw_fd(),
                name.as_ptr(),
                libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC,
            )
        })?;
        let file = unsafe { File::from_raw_fd(fd) };
        if !file.metadata()?.is_file() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "only regular files may be copied",
            ));
        }
        Ok(file)
    }

    pub(super) fn read(&self, path: &Path) -> io::Result<Vec<u8>> {
        let (parent, name) = self.parent(path, false)?;
        let mut bytes = Vec::new();
        parent.read_file(&name)?.read_to_end(&mut bytes)?;
        Ok(bytes)
    }

    pub(super) fn exists(&self, path: &Path) -> io::Result<bool> {
        let (parent, name) = match self.parent(path, false) {
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(false),
            other => other?,
        };
        match parent.kind(&name) {
            Ok(_) => Ok(true),
            Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(false),
            Err(e) => Err(e),
        }
    }

    fn kind(&self, name: &OsStr) -> io::Result<libc::mode_t> {
        let name = cstr(name)?;
        let mut st = std::mem::MaybeUninit::<libc::stat>::uninit();
        cvt(unsafe {
            libc::fstatat(
                self.0.as_raw_fd(),
                name.as_ptr(),
                st.as_mut_ptr(),
                libc::AT_SYMLINK_NOFOLLOW,
            )
        })?;
        Ok(unsafe { st.assume_init() }.st_mode & libc::S_IFMT)
    }

    pub(super) fn write(&self, path: &Path, mut src: impl Read, mode: u32) -> io::Result<()> {
        let (parent, name) = self.parent(path, true)?;
        let (temp, mut file) = loop {
            let temp = unique();
            let ctemp = cstr(&temp)?;
            let fd = unsafe {
                libc::openat(
                    parent.0.as_raw_fd(),
                    ctemp.as_ptr(),
                    libc::O_WRONLY
                        | libc::O_CREAT
                        | libc::O_EXCL
                        | libc::O_NOFOLLOW
                        | libc::O_CLOEXEC,
                    0o600,
                )
            };
            if fd >= 0 {
                break (temp, unsafe { File::from_raw_fd(fd) });
            }
            if io::Error::last_os_error().kind() != io::ErrorKind::AlreadyExists {
                return Err(io::Error::last_os_error());
            }
        };
        let result = (|| {
            io::copy(&mut src, &mut file)?;
            file.flush()?;
            file.set_permissions(std::fs::Permissions::from_mode(mode))?;
            parent.rename(&temp, &parent, &name)
        })();
        if result.is_err() {
            let _ = parent.remove_name(&temp);
        }
        result
    }

    pub(super) fn copy_file(
        &self,
        src: &Dir,
        from: &Path,
        to: &Path,
        readonly: bool,
    ) -> io::Result<()> {
        let (source, name) = src.parent(from, false)?;
        let mode = if readonly { 0o444 } else { 0o644 };
        self.write(to, source.read_file(&name)?, mode)
    }

    fn names(&self) -> io::Result<Vec<OsString>> {
        // Reopen '.', rather than dup: dup would share the directory offset.
        let fd = self.child(OsStr::new("."), false)?.0;
        use std::os::fd::IntoRawFd;
        let fd = fd.into_raw_fd();
        let ptr = unsafe { libc::fdopendir(fd) };
        if ptr.is_null() {
            let error = io::Error::last_os_error();
            unsafe {
                libc::close(fd);
            }
            return Err(error);
        }
        struct Stream(*mut libc::DIR);
        impl Drop for Stream {
            fn drop(&mut self) {
                unsafe {
                    libc::closedir(self.0);
                }
            }
        }
        let stream = Stream(ptr);
        let mut names = Vec::new();
        loop {
            // readdir_r reports errors separately from end-of-stream. The
            // platform dirent has room for the platform's maximum filename.
            let mut entry = std::mem::MaybeUninit::<libc::dirent>::uninit();
            let mut result = std::ptr::null_mut();
            let rc = unsafe { libc::readdir_r(stream.0, entry.as_mut_ptr(), &mut result) };
            if rc != 0 {
                return Err(io::Error::from_raw_os_error(rc));
            }
            if result.is_null() {
                break;
            }
            let name = unsafe { CStr::from_ptr((*result).d_name.as_ptr()) }.to_bytes();
            if name != b"." && name != b".." {
                names.push(OsString::from_vec(name.to_vec()));
            }
        }
        Ok(names)
    }

    pub(super) fn copy_tree(&self, src: &Dir, path: &Path) -> io::Result<()> {
        let source = src.subdir(path, false)?;
        self.subdir(path, true)?.copy_contents(&source, false)
    }

    fn copy_contents(&self, src: &Dir, readonly: bool) -> io::Result<()> {
        for name in src.names()? {
            if name == ".lake" || name == "target" || name == ".djinn" {
                continue;
            }
            match src.kind(&name)? {
                libc::S_IFDIR => self
                    .child(&name, true)?
                    .copy_contents(&src.child(&name, false)?, readonly)?,
                libc::S_IFREG => {
                    self.copy_file(src, Path::new(&name), Path::new(&name), readonly)?
                }
                _ => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!(
                            "refusing symlink or special file: {}",
                            name.to_string_lossy()
                        ),
                    ))
                }
            }
        }
        Ok(())
    }

    fn rename(&self, from: &OsStr, dest: &Dir, to: &OsStr) -> io::Result<()> {
        let from = cstr(from)?;
        let to = cstr(to)?;
        cvt(unsafe {
            libc::renameat(
                self.0.as_raw_fd(),
                from.as_ptr(),
                dest.0.as_raw_fd(),
                to.as_ptr(),
            )
        })
        .map(|_| ())
    }

    pub(super) fn move_path(&self, from: &Path, to: &Path) -> io::Result<()> {
        let (source, from) = self.parent(from, false)?;
        let (dest, to) = self.parent(to, true)?;
        source.rename(&from, &dest, &to)
    }

    /// Prepare a complete replacement before touching the existing tree, and
    /// restore the old tree if installing the replacement fails.
    pub(super) fn mirror_tree(
        &self,
        src: &Dir,
        path: &Path,
        readonly: bool,
    ) -> io::Result<()> {
        let (parent, name) = self.parent(path, true)?;
        let temp = parent.unique_dir()?;
        let result = (|| {
            parent
                .child(&temp, false)?
                .copy_contents(&src.subdir(path, false)?, readonly)?;
            let old = parent.unique_dir()?;
            parent.remove_name(&old)?;
            let had_old = match parent.rename(&name, &parent, &old) {
                Ok(()) => true,
                Err(e) if e.kind() == io::ErrorKind::NotFound => false,
                Err(e) => return Err(e),
            };
            if let Err(error) = parent.rename(&temp, &parent, &name) {
                if had_old {
                    parent.rename(&old, &parent, &name).map_err(|rollback| {
                        io::Error::other(format!(
                            "{error}; rollback failed: {rollback}; previous tree remains at {}",
                            old.to_string_lossy()
                        ))
                    })?;
                }
                return Err(error);
            }
            if had_old {
                parent.remove_name(&old)?;
            }
            Ok(())
        })();
        if result.is_err() {
            let _ = parent.remove_name(&temp);
        }
        result
    }

    fn unique_dir(&self) -> io::Result<OsString> {
        loop {
            let name = unique();
            let cname = cstr(&name)?;
            if unsafe { libc::mkdirat(self.0.as_raw_fd(), cname.as_ptr(), 0o700) } == 0 {
                return Ok(name);
            }
            if io::Error::last_os_error().kind() != io::ErrorKind::AlreadyExists {
                return Err(io::Error::last_os_error());
            }
        }
    }

    fn remove_name(&self, name: &OsStr) -> io::Result<()> {
        let kind = match self.kind(name) {
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
            other => other?,
        };
        let flags = if kind == libc::S_IFDIR {
            let dir = self.child(name, false)?;
            for entry in dir.names()? {
                dir.remove_name(&entry)?;
            }
            libc::AT_REMOVEDIR
        } else {
            0
        };
        let name = cstr(name)?;
        cvt(unsafe { libc::unlinkat(self.0.as_raw_fd(), name.as_ptr(), flags) }).map(|_| ())
    }

    pub(super) fn remove(&self, path: &Path) -> io::Result<()> {
        let (parent, name) = match self.parent(path, false) {
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
            other => other?,
        };
        parent.remove_name(&name)
    }
}

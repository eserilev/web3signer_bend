# The foreign effects of Bulkhead. The C code is in src/ffi/. A build must
# compile the generated C with -I src/ffi and the blst include path, and link
# libblst, libcrypto and libicuuc: see build.sh.
#
# Secret keys stay in C memory. Bend code refers to a key by its index.
import Base

# Decrypts an EIP-2335 keystore and returns the index of its key. kdf is
# "scrypt" or "pbkdf2". For scrypt, n, r and p are its parameters. For
# pbkdf2, n is the iteration count c, and r and p are ignored.
def Keys.decrypt(kdf: String, dklen: U32, n: U32, r: U32, p: U32, salt: String, checksum: String,
  cipher: String, iv: String, password: String) -> IO(Result<&1, &1, U32 & String, U32>):
  import "./ffi/keys_decrypt.c"

# Adds a raw secret key (32 bytes of hex) and returns its index.
def Keys.load_raw(hex: String) -> IO(Result<&1, &1, U32 & String, U32>):
  import "./ffi/keys_load_raw.c"

# The compressed public key of a key index, as 0x hex.
def Keys.pubkey(index: U32) -> IO(Result<&1, &1, U32 & String, String>):
  import "./ffi/keys_pubkey.c"

# Signs a signing root (0x hex) with a key index. Returns the signature as
# 0x hex.
def Bls.sign_key(index: U32, root: String) -> IO(Result<&1, &1, U32 & String, String>):
  import "./ffi/bls_sign_key.c"

# Appends text to a file and calls fsync before it returns.
def Log.append_sync(path: String, text: String) -> IO(Result<&1, &1, U32 & String, Unit>):
  import "./ffi/log_append_sync.c"

# The whole content of a file.
def Fs.read_text(path: String) -> IO(Result<&1, &1, U32 & String, String>):
  import "./ffi/fs_read_text.c"

# The visible names in a directory, sorted, one per line.
def Fs.list(path: String) -> IO(Result<&1, &1, U32 & String, String>):
  import "./ffi/fs_list.c"

# Calls fsync on a directory.
def Fs.sync_dir(path: String) -> IO(Result<&1, &1, U32 & String, Unit>):
  import "./ffi/fs_sync_dir.c"

# Listens on an IPv4 address and port.
def Net.listen(host: String, port: U32) -> IO(Result<&1, &1, U32 & String, Listener>):
  import "./ffi/net_listen.c"

# Cuts a file to size bytes and calls fsync.
def Log.truncate_sync(path: String, size: U32) -> IO(Result<&1, &1, U32 & String, Unit>):
  import "./ffi/log_truncate_sync.c"

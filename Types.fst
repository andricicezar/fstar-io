module Types

(** this file contains types that have a direct equivalent in OCaml **)

type file_descr = int

type error = 
  | EAGAIN
  | ENOENT

type open_flag = 
  | O_RDONLY
  | O_WRONLY
  | O_RDWR
  | O_NONBLOCK	
  | O_APPEND	
  | O_CREAT	
  | O_TRUNC	
  | O_EXCL	
  | O_NOCTTY	
  | O_DSYNC	
  | O_SYNC	
  | O_RSYNC
  | O_SHARE_DELETE
  | O_CLOEXEC
  | O_KEEPEXEC

type socket_bool_option = 
  | SO_DEBUG
  | SO_BROADCAST
  | SO_REUSEADDR
  | SO_KEEPALIVE
  | SO_DONTROUTE
  | SO_OOBINLINE
  | SO_ACCEPTCONN
  | TCP_NODELAY
  | IPV6_ONLY

type access_permission =
  | R_OK
  | W_OK
  | X_OK
  | F_OK

type file_kind = 
| S_REG	(* Regular file *)
| S_DIR	(* Directory *)
| S_CHR	(* Character device *)
| S_BLK	(* Block device *)
| S_LNK	(* Symbolic link *)
| S_FIFO (* Named pipe *)
| S_SOCK  (* Socket *)

type stats = {
  st_dev : Int32.t; (* Device number *)
  st_ino : Int32.t; (* Inode number *)
  st_kind : file_kind; (* Kind of the file *)
  // st_perm : file_perm; (* Access rights *)
  st_nlink : Int32.t; (* Number of links *)
  st_uid : Int32.t; (* User id of the owner *)
  st_gid : Int32.t; (* Group ID of the file's group *)
  st_rdev : Int32.t; (* Device ID (if special file) *)
  st_size : Int32.t; (* Size in bytes *)
  // st_atime : float; (* Last access time *)
  // st_mtime : float; (* Last modification time *)
  // st_ctime : float; (* Last status change time *)
}

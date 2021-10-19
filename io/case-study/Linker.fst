module Linker

open Model
open Shared
open WebServer
open Plugin

let compiled_webserver = comp.compile_prog #i #pi webserver

let whole : comp.whole_t i = 
  comp.link_t #i #pi plugin compiled_webserver

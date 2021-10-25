module Linker

open Model
open Shared
open WebServer
open Plugin
open TC.MLify.MIIO

let compiled_webserver = comp.compile_prog #i #pi webserver

let whole : comp.whole_t i = 
  comp.link_t #i #pi plugin compiled_webserver

let whole_ML = mlify #_ #(mlifyable_miio _ _) whole

let _ = 
  let _ = whole_ML () in ()

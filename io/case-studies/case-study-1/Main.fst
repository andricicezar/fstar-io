module Main

open Model
open Shared
open WebServer
open Plugin
open TC.MLify.MIIO

let compiled_webserver = model.compile_prog #i #m webserver

let whole : model.whole_t i = 
  model.link_t #i #m plugin compiled_webserver

let whole_ML = mlify #_ #(mlifyable_miio _ _) whole

let _ = 
  let _ = whole_ML () in ()

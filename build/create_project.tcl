# Define variables

set project_directory [file dirname [info script]]
set project_name  "flowcutter"
set design_timing_xdc_file  [file join $project_directory "circuit_timing.xdc"]

# Create project

create_project -force $project_name $project_directory

set board_part "em.avnet.com:ultra96v1:part0:1.2"

set_property "default_lib"        "xil_defaultlib"  [current_project]
set_property "simulator_language" "Mixed"           [current_project]
set_property "target_language"    "Verilog"         [current_project]

if {[string equal [get_filesets -quiet sources_1] ""]} {
  create_fileset -srcset sources_1
}

if {[string equal [get_filesets -quiet constrs_1] ""]} {
  create_fileset -constrset constrs_1
}

if {[string equal [get_filesets -quiet sim_1] ""]} {
  create_fileset -simset sim_1
}

# Design run synth_1

set synth_1_flow "Vivado Synthesis 2015"
set synth_1_strategy "Vivado Synthesis Defaults"
if {[string equal [get_runs -quiet synth_1] ""]} {
  create_run -name synth_1 -flow $synth_1_flow -strategy $synth_1_strategy -constrset constrs_1
} else {
  set_property flow     $synth_1_flow     [get_runs synth_1]
  set_property strategy $synth_1_strategy [get_runs synth_1]
}

current_run -synthesis [get_runs synth_1]

# Design run impl_1

set impl_1_flow      "Vivado Implementation 2015"
set impl_1_strategy  "Vivado Implementation Defaults"
if {[string equal [get_runs -quiet impl_1] ""]} {
  create_run -name impl_1 -flow $impl_1_flow -strategy $impl_1_strategy -constrset constrs_1 -parent_run synth_1
} else {
  set_property flow     $impl_1_flow      [get_runs impl_1]
  set_property strategy $impl_1_strategy  [get_runs impl_1]
}
current_run -implementation [get_runs impl_1]

# Add files

if {[info exists design_timing_xdc_file]} {
  add_files -fileset constrs_1 -norecurse $design_timing_xdc_file
}

if {[info exists design_bd_tcl_file]} {
  source $design_bd_tcl_file
  regenerate_bd_layout
  save_bd_design
  set design_bd_name [get_bd_design]
  make_wrapper -files [get_files $design_bd_name.bd] -top -import
}

proc add_verilog_file {fileset_name library_name file_name} {
  set file [file normalize $file_name]
  set fileset [get_filesets $fileset_name]
  add_files -norecurse -fileset $fileset $file
  set file_obj [get_files -of_objects $fileset $file]
  set_property "file_type" "Verilog" $file_obj
}

add_verilog_file sources_1 WORK [file join $project_directory "circuit.v"]

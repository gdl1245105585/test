

`include "axi/typedef.svh"
import axi_pkg::*;
// verilog_lint: waive-start package-filename
package snitch_cluster_pkg;

  localparam int unsigned NrCores = 9;
  localparam int unsigned NrHives = 1;

  localparam int unsigned AddrWidth = 48;
  localparam int unsigned NarrowDataWidth = 64;
  localparam int unsigned WideDataWidth = 512;

  localparam int unsigned NarrowIdWidthIn = 2;
  localparam int unsigned NrMasters = 3;
  localparam int unsigned NarrowIdWidthOut = $clog2(NrMasters) + NarrowIdWidthIn;

  localparam int unsigned NrDmaMasters = 2 + 1;
  localparam int unsigned WideIdWidthIn = 1;
  localparam int unsigned WideIdWidthOut = $clog2(NrDmaMasters) + WideIdWidthIn;

  localparam int unsigned NarrowUserWidth = 1;
  localparam int unsigned WideUserWidth = 1;

  localparam int unsigned ICacheLineWidth [NrHives] = '{
    256
};
  localparam int unsigned ICacheLineCount [NrHives] = '{
    128
};
  localparam int unsigned ICacheSets [NrHives] = '{
    2
};

  localparam int unsigned Hive [NrCores] = '{0, 0, 0, 0, 0, 0, 0, 0, 0};

  typedef struct packed {
    logic [0:0] reserved;
  } sram_cfg_t;

  typedef struct packed {
    sram_cfg_t icache_tag;
    sram_cfg_t icache_data;
    sram_cfg_t tcdm;
  } sram_cfgs_t;

  typedef logic [AddrWidth-1:0]         addr_t;
  typedef logic [NarrowDataWidth-1:0]   data_t;
  typedef logic [NarrowDataWidth/8-1:0] strb_t;
  typedef logic [WideDataWidth-1:0]     data_dma_t;
  typedef logic [WideDataWidth/8-1:0]   strb_dma_t;
  typedef logic [NarrowIdWidthIn-1:0]   narrow_in_id_t;
  typedef logic [NarrowIdWidthOut-1:0]  narrow_out_id_t;
  typedef logic [WideIdWidthIn-1:0]     wide_in_id_t;
  typedef logic [WideIdWidthOut-1:0]    wide_out_id_t;
  typedef logic [NarrowUserWidth-1:0]   user_t;
  typedef logic [WideUserWidth-1:0]     user_dma_t;

  `AXI_TYPEDEF_ALL(narrow_in, addr_t, narrow_in_id_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_ALL(narrow_out, addr_t, narrow_out_id_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_ALL(wide_in, addr_t, wide_in_id_t, data_dma_t, strb_dma_t, user_dma_t)
  `AXI_TYPEDEF_ALL(wide_out, addr_t, wide_out_id_t, data_dma_t, strb_dma_t, user_dma_t)

  function automatic snitch_pma_pkg::rule_t [snitch_pma_pkg::NrMaxRules-1:0] get_cached_regions();
    automatic snitch_pma_pkg::rule_t [snitch_pma_pkg::NrMaxRules-1:0] cached_regions;
    cached_regions = '{default: '0};
    cached_regions[0] = '{base: 48'h80000000, mask: 48'hffff80000000};
    return cached_regions;
  endfunction

  localparam snitch_pma_pkg::snitch_pma_t SnitchPMACfg = '{
      NrCachedRegionRules: 1,
      CachedRegion: get_cached_regions(),
      default: 0
  };

  localparam fpnew_pkg::fpu_implementation_t FPUImplementation [9] = '{
    '{
        PipeRegs: // FMA Block
                  '{
                    '{  3, // FP32
                        3, // FP64
                        2, // FP16
                        1, // FP8
                        2, // FP16alt
                        1  // FP8alt
                      },
                    '{1, 1, 1, 1, 1, 1},   // DIVSQRT
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // NONCOMP
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // CONV
                    '{2,
                      2,
                      2,
                      2,
                      2,
                      2}    // DOTP
                    },
        UnitTypes: '{'{fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED},  // FMA
                    '{fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED}, // DIVSQRT
                    '{fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL}, // NONCOMP
                    '{fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED},   // CONV
                    '{fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED}},  // DOTP
        PipeConfig: fpnew_pkg::BEFORE
    },
    '{
        PipeRegs: // FMA Block
                  '{
                    '{  3, // FP32
                        3, // FP64
                        2, // FP16
                        1, // FP8
                        2, // FP16alt
                        1  // FP8alt
                      },
                    '{1, 1, 1, 1, 1, 1},   // DIVSQRT
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // NONCOMP
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // CONV
                    '{2,
                      2,
                      2,
                      2,
                      2,
                      2}    // DOTP
                    },
        UnitTypes: '{'{fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED},  // FMA
                    '{fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED}, // DIVSQRT
                    '{fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL}, // NONCOMP
                    '{fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED},   // CONV
                    '{fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED}},  // DOTP
        PipeConfig: fpnew_pkg::BEFORE
    },
    '{
        PipeRegs: // FMA Block
                  '{
                    '{  3, // FP32
                        3, // FP64
                        2, // FP16
                        1, // FP8
                        2, // FP16alt
                        1  // FP8alt
                      },
                    '{1, 1, 1, 1, 1, 1},   // DIVSQRT
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // NONCOMP
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // CONV
                    '{2,
                      2,
                      2,
                      2,
                      2,
                      2}    // DOTP
                    },
        UnitTypes: '{'{fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED},  // FMA
                    '{fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED}, // DIVSQRT
                    '{fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL}, // NONCOMP
                    '{fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED},   // CONV
                    '{fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED}},  // DOTP
        PipeConfig: fpnew_pkg::BEFORE
    },
    '{
        PipeRegs: // FMA Block
                  '{
                    '{  3, // FP32
                        3, // FP64
                        2, // FP16
                        1, // FP8
                        2, // FP16alt
                        1  // FP8alt
                      },
                    '{1, 1, 1, 1, 1, 1},   // DIVSQRT
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // NONCOMP
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // CONV
                    '{2,
                      2,
                      2,
                      2,
                      2,
                      2}    // DOTP
                    },
        UnitTypes: '{'{fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED},  // FMA
                    '{fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED}, // DIVSQRT
                    '{fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL}, // NONCOMP
                    '{fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED},   // CONV
                    '{fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED}},  // DOTP
        PipeConfig: fpnew_pkg::BEFORE
    },
    '{
        PipeRegs: // FMA Block
                  '{
                    '{  3, // FP32
                        3, // FP64
                        2, // FP16
                        1, // FP8
                        2, // FP16alt
                        1  // FP8alt
                      },
                    '{1, 1, 1, 1, 1, 1},   // DIVSQRT
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // NONCOMP
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // CONV
                    '{2,
                      2,
                      2,
                      2,
                      2,
                      2}    // DOTP
                    },
        UnitTypes: '{'{fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED},  // FMA
                    '{fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED}, // DIVSQRT
                    '{fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL}, // NONCOMP
                    '{fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED},   // CONV
                    '{fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED}},  // DOTP
        PipeConfig: fpnew_pkg::BEFORE
    },
    '{
        PipeRegs: // FMA Block
                  '{
                    '{  3, // FP32
                        3, // FP64
                        2, // FP16
                        1, // FP8
                        2, // FP16alt
                        1  // FP8alt
                      },
                    '{1, 1, 1, 1, 1, 1},   // DIVSQRT
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // NONCOMP
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // CONV
                    '{2,
                      2,
                      2,
                      2,
                      2,
                      2}    // DOTP
                    },
        UnitTypes: '{'{fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED},  // FMA
                    '{fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED}, // DIVSQRT
                    '{fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL}, // NONCOMP
                    '{fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED},   // CONV
                    '{fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED}},  // DOTP
        PipeConfig: fpnew_pkg::BEFORE
    },
    '{
        PipeRegs: // FMA Block
                  '{
                    '{  3, // FP32
                        3, // FP64
                        2, // FP16
                        1, // FP8
                        2, // FP16alt
                        1  // FP8alt
                      },
                    '{1, 1, 1, 1, 1, 1},   // DIVSQRT
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // NONCOMP
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // CONV
                    '{2,
                      2,
                      2,
                      2,
                      2,
                      2}    // DOTP
                    },
        UnitTypes: '{'{fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED},  // FMA
                    '{fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED}, // DIVSQRT
                    '{fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL}, // NONCOMP
                    '{fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED},   // CONV
                    '{fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED}},  // DOTP
        PipeConfig: fpnew_pkg::BEFORE
    },
    '{
        PipeRegs: // FMA Block
                  '{
                    '{  3, // FP32
                        3, // FP64
                        2, // FP16
                        1, // FP8
                        2, // FP16alt
                        1  // FP8alt
                      },
                    '{1, 1, 1, 1, 1, 1},   // DIVSQRT
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // NONCOMP
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // CONV
                    '{2,
                      2,
                      2,
                      2,
                      2,
                      2}    // DOTP
                    },
        UnitTypes: '{'{fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED},  // FMA
                    '{fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED}, // DIVSQRT
                    '{fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL}, // NONCOMP
                    '{fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED},   // CONV
                    '{fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED}},  // DOTP
        PipeConfig: fpnew_pkg::BEFORE
    },
    '{
        PipeRegs: // FMA Block
                  '{
                    '{  3, // FP32
                        3, // FP64
                        2, // FP16
                        1, // FP8
                        2, // FP16alt
                        1  // FP8alt
                      },
                    '{1, 1, 1, 1, 1, 1},   // DIVSQRT
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // NONCOMP
                    '{1,
                      1,
                      1,
                      1,
                      1,
                      1},   // CONV
                    '{2,
                      2,
                      2,
                      2,
                      2,
                      2}    // DOTP
                    },
        UnitTypes: '{'{fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED,
                       fpnew_pkg::MERGED},  // FMA
                    '{fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED}, // DIVSQRT
                    '{fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL,
                        fpnew_pkg::PARALLEL}, // NONCOMP
                    '{fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED,
                        fpnew_pkg::MERGED},   // CONV
                    '{fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED,
                        fpnew_pkg::DISABLED}}, // DOTP
        PipeConfig: fpnew_pkg::BEFORE
    }
  };

  localparam snitch_ssr_pkg::ssr_cfg_t [3-1:0] SsrCfgs [9] = '{
    '{'{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3},
      '{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3},
      '{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3}},
    '{'{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3},
      '{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3},
      '{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3}},
    '{'{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3},
      '{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3},
      '{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3}},
    '{'{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3},
      '{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3},
      '{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3}},
    '{'{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3},
      '{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3},
      '{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3}},
    '{'{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3},
      '{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3},
      '{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3}},
    '{'{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3},
      '{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3},
      '{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3}},
    '{'{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3},
      '{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3},
      '{0, 0, 0, 0, 1, 1, 4, 14, 17, 3, 4, 3, 8, 4, 3}},
    '{/*None*/ '0,
      /*None*/ '0,
      /*None*/ '0}
  };

  localparam logic [3-1:0][4:0] SsrRegs [9] = '{
    '{2, 1, 0},
    '{2, 1, 0},
    '{2, 1, 0},
    '{2, 1, 0},
    '{2, 1, 0},
    '{2, 1, 0},
    '{2, 1, 0},
    '{2, 1, 0},
    '{/*None*/ 0, /*None*/ 0, /*None*/ 0}
  };

endpackage
// verilog_lint: waive-stop package-filename

module ysyx_050228 (
    input  clock,  
    input  reset,


    input           io_interrupt,

    input 	        io_master_awready, 			
	output 	        io_master_awvalid ,			
	output [3:0] 	io_master_awid,	
	output [31:0] 	io_master_awaddr,			
	output [7:0] 	io_master_awlen,			
	output [2:0] 	io_master_awsize,			
	output [1:0] 	io_master_awburst,			
	input 	        io_master_wready,	
	output 	        io_master_wvalid,	
	output [63:0] 	io_master_wdata,			
	output [7:0] 	io_master_wstrb,			
	output 	        io_master_wlast,	
	output 	        io_master_bready,	
	input 	        io_master_bvalid,	
	input [3:0] 	io_master_bid,	
	input [1:0] 	io_master_bresp,		
	input 	        io_master_arready,	
	output 	        io_master_arvalid,	
	output [3:0] 	io_master_arid,		
	output [31:0] 	io_master_araddr,			
	output [7:0] 	io_master_arlen,			
	output [2:0] 	io_master_arsize,			
	output [1:0] 	io_master_arburst,			
	output 	        io_master_rready,		
	input 	        io_master_rvalid,		
	input [3:0] 	io_master_rid,		
	input [1:0] 	io_master_rresp,			
	input [63:0] 	io_master_rdata,		
	input 	        io_master_rlast,

    output          io_slave_awready ,
    input           io_slave_awvalid ,
    input [3:0]     io_slave_awid ,
    input [31:0]    io_slave_awaddr ,
    input [7:0]     io_slave_awlen ,
    input [2:0]     io_slave_awsize ,
    input [1:0]     io_slave_awburst ,
    output          io_slave_wready ,
    input           io_slave_wvalid ,
    input [63:0]    io_slave_wdata ,
    input [7:0]     io_slave_wstrb ,
    input           io_slave_wlast ,
    input           io_slave_bready ,
    output          io_slave_bvalid ,
    output [3:0]    io_slave_bid ,
    output [1:0]    io_slave_bresp ,
    output          io_slave_arready ,
    input           io_slave_arvalid ,
    input [3:0]     io_slave_arid ,
    input [31:0]    io_slave_araddr ,
    input [7:0]     io_slave_arlen ,
    input [2:0]     io_slave_arsize ,
    input [1:0]     io_slave_arburst ,
    input           io_slave_rready ,
    output          io_slave_rvalid ,
    output [3:0]    io_slave_rid ,
    output [1:0]    io_slave_rresp ,
    output [63:0]   io_slave_rdata ,
    output          io_slave_rlast ,
    
    output [5:0]    io_sram0_addr ,
    output          io_sram0_cen ,
    output          io_sram0_wen ,
    output [127:0]  io_sram0_wmask ,
    output [127:0]  io_sram0_wdata ,
    input [127:0]   io_sram0_rdata ,
    output [5:0]    io_sram1_addr ,
    output          io_sram1_cen ,
    output          io_sram1_wen ,
    output [127:0]  io_sram1_wmask ,
    output [127:0]  io_sram1_wdata ,
    input [127:0]   io_sram1_rdata ,
    output [5:0]    io_sram2_addr ,
    output          io_sram2_cen ,
    output          io_sram2_wen ,
    output [127:0]  io_sram2_wmask ,
    output [127:0]  io_sram2_wdata ,
    input [127:0]   io_sram2_rdata ,
    output [5:0]    io_sram3_addr ,
    output          io_sram3_cen ,
    output          io_sram3_wen ,
    output [127:0]  io_sram3_wmask ,
    output [127:0]  io_sram3_wdata ,
    input [127:0]   io_sram3_rdata ,
    output [5:0]    io_sram4_addr ,
    output          io_sram4_cen ,
    output          io_sram4_wen ,
    output [127:0]  io_sram4_wmask ,
    output [127:0]  io_sram4_wdata ,
    input [127:0]   io_sram4_rdata ,
    output [5:0]    io_sram5_addr ,
    output          io_sram5_cen ,
    output          io_sram5_wen ,
    output [127:0]  io_sram5_wmask ,
    output [127:0]  io_sram5_wdata ,
    input [127:0]   io_sram5_rdata ,
    output [5:0]    io_sram6_addr ,
    output          io_sram6_cen ,
    output          io_sram6_wen ,
    output [127:0]  io_sram6_wmask ,
    output [127:0]  io_sram6_wdata ,
    input [127:0]   io_sram6_rdata ,
    output [5:0]    io_sram7_addr ,
    output          io_sram7_cen ,
    output          io_sram7_wen ,
    output [127:0]  io_sram7_wmask ,
    output [127:0]  io_sram7_wdata ,
    input [127:0]   io_sram7_rdata

);

// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// AUTOMATICALLY GENERATED by clustergen.py; edit the script or configuration
// instead.









// verilog_lint: waive-start package-filename


snitch_cluster_wrapper i_cluster (
    .clk_i(clock),
    .rst_ni(~reset),
    .debug_req_i('d0),
    .meip_i('d0),
    .mtip_i('d0),
    .msip_i('d0),
    .narrow_in_req_i(narrow_in_req_i),
    .narrow_in_resp_o(narrow_in_resp_o),
    .narrow_out_req_o(narrow_out_req_o),
    .narrow_out_resp_i(narrow_out_resp_i),
    .wide_out_req_o(wide_out_req_o),
    .wide_out_resp_i(wide_out_resp_i),
    .wide_in_req_i(wide_in_req_i),
    .wide_in_resp_o(wide_in_resp_o)
);

axicb_crossbar_lite_top axicb_crossbar_lite_top
(
.slv0_aclk(clock),
.slv0_aresetn(~reset),
.slv0_srst(reset),
.slv0_awvalid(narrow_out_req_o.aw_valid),
.slv0_awready(narrow_out_resp_i.aw_ready),
.slv0_awaddr(narrow_out_req_o.aw.addr),
.slv0_awprot(narrow_out_req_o.aw.prot),
.slv0_awid(narrow_out_req_o.aw.id),
.slv0_awuser(narrow_out_req_o.aw.user),
.slv0_wvalid(narrow_out_req_o.w_valid),
.slv0_wready(narrow_out_resp_i.w_ready),
.slv0_wdata(narrow_out_req_o.w.data),
.slv0_wstrb(narrow_out_req_o.w.strb),
.slv0_wuser(narrow_out_req_o.w.user),
.slv0_bvalid(narrow_out_resp_i.b_valid),
.slv0_bready(narrow_out_req_o.b_ready),
.slv0_bid(narrow_out_resp_i.b.id),
.slv0_bresp(narrow_out_resp_i.b.resp),
.slv0_buser(narrow_out_resp_i.b.user),
.slv0_arvalid(narrow_out_req_o.ar_valid),
.slv0_arready(narrow_out_resp_i.ar_ready),
.slv0_araddr(narrow_out_req_o.ar.addr),
.slv0_arprot(narrow_out_req_o.ar.prot),
.slv0_arid(narrow_out_req_o.ar.id),
.slv0_aruser(narrow_out_req_o.ar.user),
.slv0_rvalid(narrow_out_resp_i.r_valid),
.slv0_rready(narrow_out_req_o.r_ready),
.slv0_rid(narrow_out_resp_i.r.id),
.slv0_rresp(narrow_out_resp_i.r.resp),
.slv0_rdata(narrow_out_resp_i.r.data),
.slv0_ruser(narrow_out_resp_i.r.user),
.slv1_aclk(clock),
.slv1_aresetn(~reset),
.slv1_srst(reset),
.slv1_awvalid(wide_out_req_o.aw_valid),
.slv1_awready(wide_out_resp_i.aw_ready),
.slv1_awaddr(wide_out_req_o.aw.addr),
.slv1_awprot(wide_out_req_o.aw.prot),
.slv1_awid(wide_out_req_o.aw.id),
.slv1_awuser(wide_out_req_o.aw.user),
.slv1_wvalid(wide_out_req_o.w_valid),
.slv1_wready(wide_out_resp_i.w_ready),
.slv1_wdata(wide_out_req_o.w.data),
.slv1_wstrb(wide_out_req_o.w.strb),
.slv1_wuser(wide_out_req_o.w.user),
.slv1_bvalid(wide_out_resp_i.b_valid),
.slv1_bready(wide_out_req_o.b_ready),
.slv1_bid(wide_out_resp_i.b.id),
.slv1_bresp(wide_out_resp_i.b.resp),
.slv1_buser(wide_out_resp_i.b.user),
.slv1_arvalid(wide_out_req_o.ar_valid),
.slv1_arready(wide_out_resp_i.ar_ready),
.slv1_araddr(wide_out_req_o.ar.addr),
.slv1_arprot(wide_out_req_o.ar.prot),
.slv1_arid(wide_out_req_o.ar.id),
.slv1_aruser(wide_out_req_o.ar.user),
.slv1_rvalid(wide_out_resp_i.r_valid),
.slv1_rready(wide_out_req_o.r_ready),
.slv1_rid(wide_out_resp_i.r.id),
.slv1_rresp(wide_out_resp_i.r.resp),
.slv1_rdata(wide_out_resp_i.r.data),
.slv1_ruser(wide_out_resp_i.r.user),

.mst0_aclk(clock),
.mst0_aresetn(~reset),
.mst0_srst(reset),
.mst0_awvalid(io_master_awvalid),
.mst0_awready(io_master_awready),
.mst0_awaddr(io_master_awaddr),
.mst0_awprot(),
.mst0_awid(io_master_awid),
.mst0_awuser(io_master_awuser),
.mst0_wvalid(io_master_wvalid),
.mst0_wready(io_master_wready),
.mst0_wdata(io_master_wdata),
.mst0_wstrb(io_master_wstrb),
.mst0_wuser(io_master_wuser),
.mst0_bvalid(io_master_bvalid),
.mst0_bready(io_master_bready),
.mst0_bid(io_master_bid),
.mst0_bresp(io_master_bresp),
.mst0_buser(io_master_buser),
.mst0_arvalid(io_master_arvalid),
.mst0_arready(io_master_arready),
.mst0_araddr(io_master_araddr),
.mst0_arprot(),
.mst0_arid(io_master_arid),
.mst0_aruser(io_master_aruser),
.mst0_rvalid(io_master_rvalid),
.mst0_rready(io_master_rready),
.mst0_rid(io_master_rid),
.mst0_rresp(io_master_rresp),
.mst0_rdata(io_master_rdata),
.mst0_ruser(io_master_ruser)
);

  snitch_cluster_pkg::narrow_in_req_t     narrow_in_req_i;
  snitch_cluster_pkg::narrow_in_resp_t    narrow_in_resp_o;
  snitch_cluster_pkg::narrow_out_req_t    narrow_out_req_o;
  snitch_cluster_pkg::narrow_out_resp_t   narrow_out_resp_i;
  snitch_cluster_pkg::wide_out_req_t      wide_out_req_o;
  snitch_cluster_pkg::wide_out_resp_t     wide_out_resp_i;
  snitch_cluster_pkg::wide_in_req_t       wide_in_req_i;
  snitch_cluster_pkg::wide_in_resp_t      wide_in_resp_o;
endmodule;

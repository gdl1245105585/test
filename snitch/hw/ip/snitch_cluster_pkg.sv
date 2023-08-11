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


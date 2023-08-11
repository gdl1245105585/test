package axi_pkg;
    /// AXI Transaction Burst Width.
  parameter int unsigned BurstWidth  = 32'd2;
  /// AXI Transaction Response Width.
  parameter int unsigned RespWidth   = 32'd2;
  /// AXI Transaction Cacheability Width.
  parameter int unsigned CacheWidth  = 32'd4;
  /// AXI Transaction Protection Width.
  parameter int unsigned ProtWidth   = 32'd3;
  /// AXI Transaction Quality of Service Width.
  parameter int unsigned QosWidth    = 32'd4;
  /// AXI Transaction Region Width.
  parameter int unsigned RegionWidth = 32'd4;
  /// AXI Transaction Length Width.
  parameter int unsigned LenWidth    = 32'd8;
  /// AXI Transaction Size Width.
  parameter int unsigned SizeWidth   = 32'd3;
  /// AXI Lock Width.
  parameter int unsigned LockWidth   = 32'd1;
  /// AXI5 Atomic Operation Width.
  parameter int unsigned AtopWidth   = 32'd6;
  /// AXI5 Non-Secure Address Identifier.
  parameter int unsigned NsaidWidth  = 32'd4;

  /// AXI Transaction Burst Width.
  typedef logic [1:0]  burst_t;
  /// AXI Transaction Response Type.
  typedef logic [1:0]   resp_t;
  /// AXI Transaction Cacheability Type.
  typedef logic [3:0]  cache_t;
  /// AXI Transaction Protection Type.
  typedef logic [2:0]   prot_t;
  /// AXI Transaction Quality of Service Type.
  typedef logic [3:0]    qos_t;
  /// AXI Transaction Region Type.
  typedef logic [3:0] region_t;
  /// AXI Transaction Length Type.
  typedef logic [7:0]    len_t;
  /// AXI Transaction Size Type.
  typedef logic [2:0]   size_t;
  /// AXI5 Atomic Operation Type.
  typedef logic [5:0]   atop_t; // atomic operations
  /// AXI5 Non-Secure Address Identifier.
  typedef logic [3:0]  nsaid_t;

  /// In a fixed burst:
  /// - The address is the same for every transfer in the burst.
  /// - The byte lanes that are valid are constant for all beats in the burst.  However, within
  ///   those byte lanes, the actual bytes that have `wstrb` asserted can differ for each beat in
  ///   the burst.
  /// This burst type is used for repeated accesses to the same location such as when loading or
  /// emptying a FIFO.
  localparam BURST_FIXED = 2'b00;
  /// In an incrementing burst, the address for each transfer in the burst is an increment of the
  /// address for the previous transfer.  The increment value depends on the size of the transfer.
  /// For example, the address for each transfer in a burst with a size of 4 bytes is the previous
  /// address plus four.
  /// This burst type is used for accesses to normal sequential memory.
  localparam BURST_INCR  = 2'b01;
  /// A wrapping burst is similar to an incrementing burst, except that the address wraps around to
  /// a lower address if an upper address limit is reached.
  /// The following restrictions apply to wrapping bursts:
  /// - The start address must be aligned to the size of each transfer.
  /// - The length of the burst must be 2, 4, 8, or 16 transfers.
  localparam BURST_WRAP  = 2'b10;

  /// Normal access success.  Indicates that a normal access has been successful. Can also indicate
  /// that an exclusive access has failed.
  localparam RESP_OKAY   = 2'b00;
  /// Exclusive access okay.  Indicates that either the read or write portion of an exclusive access
  /// has been successful.
  localparam RESP_EXOKAY = 2'b01;
  /// Slave error.  Used when the access has reached the slave successfully, but the slave wishes to
  /// return an error condition to the originating master.
  localparam RESP_SLVERR = 2'b10;
  /// Decode error.  Generated, typically by an interconnect component, to indicate that there is no
  /// slave at the transaction address.
  localparam RESP_DECERR = 2'b11;

  /// When this bit is asserted, the interconnect, or any component, can delay the transaction
  /// reaching its final destination for any number of cycles.
  localparam CACHE_BUFFERABLE = 4'b0001;
  /// When HIGH, Modifiable indicates that the characteristics of the transaction can be modified.
  /// When Modifiable is LOW, the transaction is Non-modifiable.
  localparam CACHE_MODIFIABLE = 4'b0010;
  /// When this bit is asserted, read allocation of the transaction is recommended but is not
  /// mandatory.
  localparam CACHE_RD_ALLOC   = 4'b0100;
  /// When this bit is asserted, write allocation of the transaction is recommended but is not
  /// mandatory.
  localparam CACHE_WR_ALLOC   = 4'b1000;

  /// Maximum number of bytes per burst, as specified by `size` (see Table A3-2).
  function automatic shortint unsigned num_bytes(size_t size);
    return 1 << size;
  endfunction

  /// An overly long address type.
  /// It lets us define functions that work generically for shorter addresses.  We rely on the
  /// synthesizer to optimize the unused bits away.
  typedef logic [127:0] largest_addr_t;

  /// Aligned address of burst (see A3-51).
  function automatic largest_addr_t aligned_addr(largest_addr_t addr, size_t size);
    return (addr >> size) << size;
  endfunction

  /// Warp boundary of a `BURST_WRAP` transfer (see A3-51).
  /// This is the lowest address accessed within a wrapping burst.
  /// This address is aligned to the size and length of the burst.
  /// The length of a `BURST_WRAP` has to be 2, 4, 8, or 16 transfers.
  function automatic largest_addr_t wrap_boundary (largest_addr_t addr, size_t size, len_t len);
    largest_addr_t wrap_addr;

    // pragma translate_off
    `ifndef VERILATOR
      assume (len == len_t'(4'b1) || len == len_t'(4'b11) || len == len_t'(4'b111) ||
          len == len_t'(4'b1111)) else
        $error("AXI BURST_WRAP with not allowed len of: %0h", len);
    `endif
    // pragma translate_on

    // In A3-51 the wrap boundary is defined as:
    // `Wrap_Boundary = (INT(Start_Address / (Number_Bytes × Burst_Length))) ×
    //    (Number_Bytes × Burst_Length)`
    // Whereas the aligned address is defined as:
    // `Aligned_Address = (INT(Start_Address / Number_Bytes)) × Number_Bytes`
    // This leads to the wrap boundary using the same calculation as the aligned address, difference
    // being the additional dependency on the burst length. The addition in the case statement
    // is equal to the multiplication with `Burst_Length` as a shift (used by `aligned_addr`) is
    // equivalent with multiplication and division by a power of two, which conveniently are the
    // only allowed values for `len` of a `BURST_WRAP`.
    unique case (len)
      4'b1    : wrap_addr = (addr >> (unsigned'(size) + 1)) << (unsigned'(size) + 1); // multiply `Number_Bytes` by `2`
      4'b11   : wrap_addr = (addr >> (unsigned'(size) + 2)) << (unsigned'(size) + 2); // multiply `Number_Bytes` by `4`
      4'b111  : wrap_addr = (addr >> (unsigned'(size) + 3)) << (unsigned'(size) + 3); // multiply `Number_Bytes` by `8`
      4'b1111 : wrap_addr = (addr >> (unsigned'(size) + 4)) << (unsigned'(size) + 4); // multiply `Number_Bytes` by `16`
      default : wrap_addr = '0;
    endcase
    return wrap_addr;
  endfunction

  /// Address of beat (see A3-51).
  function automatic largest_addr_t
  beat_addr(largest_addr_t addr, size_t size, len_t len, burst_t burst, shortint unsigned i_beat);
    largest_addr_t ret_addr = addr;
    largest_addr_t wrp_bond = '0;
    if (burst == BURST_WRAP) begin
      // do not trigger the function if there is no wrapping burst, to prevent assumptions firing
      wrp_bond = wrap_boundary(addr, size, len);
    end
    if (i_beat != 0 && burst != BURST_FIXED) begin
      // From A3-51:
      // For an INCR burst, and for a WRAP burst for which the address has not wrapped, this
      // equation determines the address of any transfer after the first transfer in a burst:
      // `Address_N = Aligned_Address + (N – 1) × Number_Bytes` (N counts from 1 to len!)
      ret_addr = aligned_addr(addr, size) + i_beat * num_bytes(size);
      // From A3-51:
      // For a WRAP burst, if Address_N = Wrap_Boundary + (Number_Bytes × Burst_Length), then:
      // * Use this equation for the current transfer:
      //     `Address_N = Wrap_Boundary`
      // * Use this equation for any subsequent transfers:
      //     `Address_N = Start_Address + ((N – 1) × Number_Bytes) – (Number_Bytes × Burst_Length)`
      // This means that the address calculation of a `BURST_WRAP` fundamentally works the same
      // as for a `BURST_INC`, the difference is when the calculated address increments
      // over the wrap threshold, the address wraps around by subtracting the accessed address
      // space from the normal `BURST_INCR` address. The lower wrap boundary is equivalent to
      // The wrap trigger condition minus the container size (`num_bytes(size) * (len + 1)`).
      if (burst == BURST_WRAP && ret_addr >= wrp_bond + (num_bytes(size) * (len + 1))) begin
        ret_addr = ret_addr - (num_bytes(size) * (len + 1));
      end
    end
    return ret_addr;
  endfunction

  /// Index of lowest byte in beat (see A3-51).
  function automatic shortint unsigned
  beat_lower_byte(largest_addr_t addr, size_t size, len_t len, burst_t burst,
      shortint unsigned strobe_width, shortint unsigned i_beat);
    largest_addr_t _addr = beat_addr(addr, size, len, burst, i_beat);
    return shortint'(_addr - (_addr / strobe_width) * strobe_width);
  endfunction

  /// Index of highest byte in beat (see A3-51).
  function automatic shortint unsigned
  beat_upper_byte(largest_addr_t addr, size_t size, len_t len, burst_t burst,
      shortint unsigned strobe_width, shortint unsigned i_beat);
    if (i_beat == 0) begin
      return aligned_addr(addr, size) + (num_bytes(size) - 1) - (addr / strobe_width) * strobe_width;
    end else begin
      return beat_lower_byte(addr, size, len, burst, strobe_width, i_beat) + num_bytes(size) - 1;
    end
  endfunction

  /// Is the bufferable bit set?
  function automatic logic bufferable(cache_t cache);
    return |(cache & CACHE_BUFFERABLE);
  endfunction

  /// Is the modifiable bit set?
  function automatic logic modifiable(cache_t cache);
    return |(cache & CACHE_MODIFIABLE);
  endfunction

  /// Memory Type.
  typedef enum logic [3:0] {
    DEVICE_NONBUFFERABLE,
    DEVICE_BUFFERABLE,
    NORMAL_NONCACHEABLE_NONBUFFERABLE,
    NORMAL_NONCACHEABLE_BUFFERABLE,
    WTHRU_NOALLOCATE,
    WTHRU_RALLOCATE,
    WTHRU_WALLOCATE,
    WTHRU_RWALLOCATE,
    WBACK_NOALLOCATE,
    WBACK_RALLOCATE,
    WBACK_WALLOCATE,
    WBACK_RWALLOCATE
  } mem_type_t;

  /// Create an `AR_CACHE` field from a `mem_type_t` type.
  function automatic logic [3:0] get_arcache(mem_type_t mtype);
    unique case (mtype)
      DEVICE_NONBUFFERABLE              : return 4'b0000;
      DEVICE_BUFFERABLE                 : return 4'b0001;
      NORMAL_NONCACHEABLE_NONBUFFERABLE : return 4'b0010;
      NORMAL_NONCACHEABLE_BUFFERABLE    : return 4'b0011;
      WTHRU_NOALLOCATE                  : return 4'b1010;
      WTHRU_RALLOCATE                   : return 4'b1110;
      WTHRU_WALLOCATE                   : return 4'b1010;
      WTHRU_RWALLOCATE                  : return 4'b1110;
      WBACK_NOALLOCATE                  : return 4'b1011;
      WBACK_RALLOCATE                   : return 4'b1111;
      WBACK_WALLOCATE                   : return 4'b1011;
      WBACK_RWALLOCATE                  : return 4'b1111;
    endcase // mtype
  endfunction

  /// Create an `AW_CACHE` field from a `mem_type_t` type.
  function automatic logic [3:0] get_awcache(mem_type_t mtype);
    unique case (mtype)
      DEVICE_NONBUFFERABLE              : return 4'b0000;
      DEVICE_BUFFERABLE                 : return 4'b0001;
      NORMAL_NONCACHEABLE_NONBUFFERABLE : return 4'b0010;
      NORMAL_NONCACHEABLE_BUFFERABLE    : return 4'b0011;
      WTHRU_NOALLOCATE                  : return 4'b0110;
      WTHRU_RALLOCATE                   : return 4'b0110;
      WTHRU_WALLOCATE                   : return 4'b1110;
      WTHRU_RWALLOCATE                  : return 4'b1110;
      WBACK_NOALLOCATE                  : return 4'b0111;
      WBACK_RALLOCATE                   : return 4'b0111;
      WBACK_WALLOCATE                   : return 4'b1111;
      WBACK_RWALLOCATE                  : return 4'b1111;
    endcase // mtype
  endfunction

  /// RESP precedence: DECERR > SLVERR > OKAY > EXOKAY.  This is not defined in the AXI standard but
  /// depends on the implementation.  We consistently use the precedence above.  Rationale:
  /// - EXOKAY means an exclusive access was successful, whereas OKAY means it was not.  Thus, if
  ///   OKAY and EXOKAY are to be merged, OKAY precedes because the exclusive access was not fully
  ///   successful.
  /// - Both DECERR and SLVERR mean (part of) a transaction were unsuccessful, whereas OKAY means an
  ///   entire transaction was successful.  Thus both DECERR and SLVERR precede OKAY.
  /// - DECERR means (part of) a transactions could not be routed to a slave component, whereas
  ///   SLVERR means the transaction reached a slave component but lead to an error condition there.
  ///   Thus DECERR precedes SLVERR because DECERR happens earlier in the handling of a transaction.
  function automatic resp_t resp_precedence(resp_t resp_a, resp_t resp_b);
    unique case (resp_a)
      RESP_OKAY: begin
        // Any response except EXOKAY precedes OKAY.
        if (resp_b == RESP_EXOKAY) begin
          return resp_a;
        end else begin
          return resp_b;
        end
      end
      RESP_EXOKAY: begin
        // Any response precedes EXOKAY.
        return resp_b;
      end
      RESP_SLVERR: begin
        // Only DECERR precedes SLVERR.
        if (resp_b == RESP_DECERR) begin
          return resp_b;
        end else begin
          return resp_a;
        end
      end
      RESP_DECERR: begin
        // No response precedes DECERR.
        return resp_a;
      end
    endcase
  endfunction

  /// AW Width: Returns the width of the AW channel payload
  function automatic int unsigned aw_width(int unsigned addr_width, int unsigned id_width,
                                           int unsigned user_width );
    // Sum the individual bit widths of the signals
    return (id_width + addr_width + LenWidth + SizeWidth + BurstWidth + LockWidth + CacheWidth +
            ProtWidth + QosWidth + RegionWidth + AtopWidth + user_width );
  endfunction

  /// W Width: Returns the width of the W channel payload
  function automatic int unsigned w_width(int unsigned data_width, int unsigned user_width );
    // Sum the individual bit widths of the signals
    return (data_width + data_width / 32'd8 + 32'd1 + user_width);
    //                   ^- StrobeWidth       ^- LastWidth
  endfunction

  /// B Width: Returns the width of the B channel payload
  function automatic int unsigned b_width(int unsigned id_width, int unsigned user_width );
    // Sum the individual bit widths of the signals
    return (id_width + RespWidth + user_width);
  endfunction

  /// AR Width: Returns the width of the AR channel payload
  function automatic int unsigned ar_width(int unsigned addr_width, int unsigned id_width,
                                           int unsigned user_width );
    // Sum the individual bit widths of the signals
    return (id_width + addr_width + LenWidth + SizeWidth + BurstWidth + LockWidth + CacheWidth +
            ProtWidth + QosWidth + RegionWidth + user_width );
  endfunction

  /// R Width: Returns the width of the R channel payload
  function automatic int unsigned r_width(int unsigned data_width, int unsigned id_width,
                                          int unsigned user_width );
    // Sum the individual bit widths of the signals
    return (id_width + data_width + RespWidth + 32'd1 + user_width);
    //                                          ^- LastWidth
  endfunction

  /// Request Width: Returns the width of the request channel
  function automatic int unsigned req_width(int unsigned addr_width,    int unsigned data_width,
                                            int unsigned id_width,      int unsigned aw_user_width,
                                            int unsigned ar_user_width, int unsigned w_user_width   );
    // Sum the individual bit widths of the signals and their handshakes
    //                                                      v- valids
    return (aw_width(addr_width, id_width, aw_user_width) + 32'd1 +
            w_width(data_width, w_user_width)             + 32'd1 +
            ar_width(addr_width, id_width, ar_user_width) + 32'd1 + 32'd1 + 32'd1 );
    //                                                              ^- R,   ^- B ready
  endfunction

  /// Response Width: Returns the width of the response channel
  function automatic int unsigned rsp_width(int unsigned data_width,   int unsigned id_width,
                                            int unsigned r_user_width, int unsigned b_user_width );
    // Sum the individual bit widths of the signals and their handshakes
    //                                                    v- valids
    return (r_width(data_width, id_width, r_user_width) + 32'd1 +
            b_width(id_width, b_user_width)             + 32'd1 + 32'd1 + 32'd1 + 32'd1);
    //                                                            ^- AW,  ^- AR,  ^- W ready
  endfunction

  // ATOP[5:0]
  /// - Sends a single data value with an address.
  /// - The target swaps the value at the addressed location with the data value that is supplied in
  ///   the transaction.
  /// - The original data value at the addressed location is returned.
  /// - Outbound data size is 1, 2, 4, or 8 bytes.
  /// - Inbound data size is the same as the outbound data size.
  localparam ATOP_ATOMICSWAP  = 6'b110000;
  /// - Sends two data values, the compare value and the swap value, to the addressed location.
  ///   The compare and swap values are of equal size.
  /// - The data value at the addressed location is checked against the compare value:
  ///   - If the values match, the swap value is written to the addressed location.
  ///   - If the values do not match, the swap value is not written to the addressed location.
  /// - The original data value at the addressed location is returned.
  /// - Outbound data size is 2, 4, 8, 16, or 32 bytes.
  /// - Inbound data size is half of the outbound data size because the outbound data contains both
  ///   compare and swap values, whereas the inbound data has only the original data value.
  localparam ATOP_ATOMICCMP   = 6'b110001;
  // ATOP[5:4]
  /// Perform no atomic operation.
  localparam ATOP_NONE        = 2'b00;
  /// - Sends a single data value with an address and the atomic operation to be performed.
  /// - The target performs the operation using the sent data and value at the addressed location as
  ///   operands.
  /// - The result is stored in the address location.
  /// - A single response is given without data.
  /// - Outbound data size is 1, 2, 4, or 8 bytes.
  localparam ATOP_ATOMICSTORE = 2'b01;
  /// Sends a single data value with an address and the atomic operation to be performed.
  /// - The original data value at the addressed location is returned.
  /// - The target performs the operation using the sent data and value at the addressed location as
  ///   operands.
  /// - The result is stored in the address location.
  /// - Outbound data size is 1, 2, 4, or 8 bytes.
  /// - Inbound data size is the same as the outbound data size.
  localparam ATOP_ATOMICLOAD  = 2'b10;
  // ATOP[3]
  /// For AtomicStore and AtomicLoad transactions `AWATOP[3]` indicates the endianness that is
  /// required for the atomic operation.  The value of `AWATOP[3]` applies to arithmetic operations
  /// only and is ignored for bitwise logical operations.
  /// When deasserted, this bit indicates that the operation is little-endian.
  localparam ATOP_LITTLE_END  = 1'b0;
  /// When asserted, this bit indicates that the operation is big-endian.
  localparam ATOP_BIG_END     = 1'b1;
  // ATOP[2:0]
  /// The value in memory is added to the sent data and the result stored in memory.
  localparam ATOP_ADD   = 3'b000;
  /// Every set bit in the sent data clears the corresponding bit of the data in memory.
  localparam ATOP_CLR   = 3'b001;
  /// Bitwise exclusive OR of the sent data and value in memory.
  localparam ATOP_EOR   = 3'b010;
  /// Every set bit in the sent data sets the corresponding bit of the data in memory.
  localparam ATOP_SET   = 3'b011;
  /// The value stored in memory is the maximum of the existing value and sent data. This operation
  /// assumes signed data.
  localparam ATOP_SMAX  = 3'b100;
  /// The value stored in memory is the minimum of the existing value and sent data. This operation
  /// assumes signed data.
  localparam ATOP_SMIN  = 3'b101;
  /// The value stored in memory is the maximum of the existing value and sent data. This operation
  /// assumes unsigned data.
  localparam ATOP_UMAX  = 3'b110;
  /// The value stored in memory is the minimum of the existing value and sent data. This operation
  /// assumes unsigned data.
  localparam ATOP_UMIN  = 3'b111;
  // ATOP[5] == 1'b1 indicated that an atomic transaction has a read response
  // Ussage eg: if (req_i.aw.atop[axi_pkg::ATOP_R_RESP]) begin
  localparam ATOP_R_RESP = 32'd5;

  // `xbar_latency_e` and `xbar_cfg_t` are documented in `doc/axi_xbar.md`.
  /// Slice on Demux AW channel.
  localparam logic [9:0] DemuxAw = (1 << 9);
  /// Slice on Demux W channel.
  localparam logic [9:0] DemuxW  = (1 << 8);
  /// Slice on Demux B channel.
  localparam logic [9:0] DemuxB  = (1 << 7);
  /// Slice on Demux AR channel.
  localparam logic [9:0] DemuxAr = (1 << 6);
  /// Slice on Demux R channel.
  localparam logic [9:0] DemuxR  = (1 << 5);
  /// Slice on Mux AW channel.
  localparam logic [9:0] MuxAw   = (1 << 4);
  /// Slice on Mux W channel.
  localparam logic [9:0] MuxW    = (1 << 3);
  /// Slice on Mux B channel.
  localparam logic [9:0] MuxB    = (1 << 2);
  /// Slice on Mux AR channel.
  localparam logic [9:0] MuxAr   = (1 << 1);
  /// Slice on Mux R channel.
  localparam logic [9:0] MuxR    = (1 << 0);
  /// Latency configuration for `axi_xbar`.
  typedef enum logic [9:0] {
    NO_LATENCY    = 10'b000_00_000_00,
    CUT_SLV_AX    = DemuxAw | DemuxAr,
    CUT_MST_AX    = MuxAw | MuxAr,
    CUT_ALL_AX    = DemuxAw | DemuxAr | MuxAw | MuxAr,
    CUT_SLV_PORTS = DemuxAw | DemuxW | DemuxB | DemuxAr | DemuxR,
    CUT_MST_PORTS = MuxAw | MuxW | MuxB | MuxAr | MuxR,
    CUT_ALL_PORTS = 10'b111_11_111_11
  } xbar_latency_e;

  /// Configuration for `axi_xbar`.
  typedef struct packed {
    /// Number of slave ports of the crossbar.
    /// This many master modules are connected to it.
    int unsigned   NoSlvPorts;
    /// Number of master ports of the crossbar.
    /// This many slave modules are connected to it.
    int unsigned   NoMstPorts;
    /// Maximum number of open transactions each master connected to the crossbar can have in
    /// flight at the same time.
    int unsigned   MaxMstTrans;
    /// Maximum number of open transactions each slave connected to the crossbar can have in
    /// flight at the same time.
    int unsigned   MaxSlvTrans;
    /// Determine if the internal FIFOs of the crossbar are instantiated in fallthrough mode.
    /// 0: No fallthrough
    /// 1: Fallthrough
    bit            FallThrough;
    /// The Latency mode of the xbar. This determines if the channels on the ports have
    /// a spill register instantiated.
    /// Example configurations are provided with the enum `xbar_latency_e`.
    xbar_latency_e LatencyMode;
    /// This is the number of `axi_multicut` stages instantiated in the line cross of the channels.
    /// Having multiple stages can potentially add a large number of FFs!
    int unsigned   PipelineStages;
    /// AXI ID width of the salve ports. The ID width of the master ports is determined
    /// Automatically. See `axi_mux` for details.
    int unsigned   AxiIdWidthSlvPorts;
    /// The used ID portion to determine if a different salve is used for the same ID.
    /// See `axi_demux` for details.
    int unsigned   AxiIdUsedSlvPorts;
    /// Are IDs unique?
    bit            UniqueIds;
    /// AXI4+ATOP address field width.
    int unsigned   AxiAddrWidth;
    /// AXI4+ATOP data field width.
    int unsigned   AxiDataWidth;
    /// The number of address rules defined for routing of the transactions.
    /// Each master port can have multiple rules, should have however at least one.
    /// If a transaction can not be routed the xbar will answer with an `axi_pkg::RESP_DECERR`.
    int unsigned   NoAddrRules;
  } xbar_cfg_t;

  /// Commonly used rule types for `axi_xbar` (64-bit addresses).
  typedef struct packed {
    int unsigned idx;
    logic [63:0] start_addr;
    logic [63:0] end_addr;
  } xbar_rule_64_t;

  /// Commonly used rule types for `axi_xbar` (32-bit addresses).
  typedef struct packed {
    int unsigned idx;
    logic [31:0] start_addr;
    logic [31:0] end_addr;
  } xbar_rule_32_t;

endpackage
// Copyright (c) 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@ethz.ch>

// Description: Package with constant APB v2.0 constants

package apb_pkg;

  typedef logic [2:0]  prot_t;

  localparam RESP_OKAY   = 1'b0;
  localparam RESP_SLVERR = 1'b1;

endpackage
// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Register Package auto-generated by `reggen` containing data structure

package idma_reg64_frontend_reg_pkg;

  // Address widths within the block
  parameter int BlockAw = 6;

  ////////////////////////////
  // Typedefs for registers //
  ////////////////////////////

  typedef struct packed {
    logic [63:0] q;
  } idma_reg64_frontend_reg2hw_src_addr_reg_t;

  typedef struct packed {
    logic [63:0] q;
  } idma_reg64_frontend_reg2hw_dst_addr_reg_t;

  typedef struct packed {
    logic [63:0] q;
  } idma_reg64_frontend_reg2hw_num_bytes_reg_t;

  typedef struct packed {
    logic        q;
  } idma_reg64_frontend_logic_struct_t;

  typedef struct packed {
    idma_reg64_frontend_logic_struct_t decouple;
    idma_reg64_frontend_logic_struct_t deburst;
    idma_reg64_frontend_logic_struct_t serialize;
  } idma_reg64_frontend_reg2hw_conf_reg_t;

  typedef struct packed {
    logic [63:0] q;
    logic        re;
  } idma_reg64_frontend_reg2hw_next_id_reg_t;

  typedef struct packed {
    logic [63:0] q;
    logic        re;
  } idma_reg64_frontend_reg2hw_done_reg_t;

  typedef struct packed {
    logic        d;
  } idma_reg64_frontend_hw2reg_status_reg_t;

  typedef struct packed {
    logic [63:0] d;
  } idma_reg64_frontend_hw2reg_next_id_reg_t;

  typedef struct packed {
    logic [63:0] d;
  } idma_reg64_frontend_hw2reg_done_reg_t;

  // Register -> HW type
  typedef struct packed {
    idma_reg64_frontend_reg2hw_src_addr_reg_t src_addr; // [324:261]
    idma_reg64_frontend_reg2hw_dst_addr_reg_t dst_addr; // [260:197]
    idma_reg64_frontend_reg2hw_num_bytes_reg_t num_bytes; // [196:133]
    idma_reg64_frontend_reg2hw_conf_reg_t conf; // [132:130]
    idma_reg64_frontend_reg2hw_next_id_reg_t next_id; // [129:65]
    idma_reg64_frontend_reg2hw_done_reg_t done; // [64:0]
  } idma_reg64_frontend_reg2hw_t;

  // HW -> register type
  typedef struct packed {
    idma_reg64_frontend_hw2reg_status_reg_t status; // [128:128]
    idma_reg64_frontend_hw2reg_next_id_reg_t next_id; // [127:64]
    idma_reg64_frontend_hw2reg_done_reg_t done; // [63:0]
  } idma_reg64_frontend_hw2reg_t;

  // Register offsets
  parameter logic [BlockAw-1:0] IDMA_REG64_FRONTEND_SRC_ADDR_OFFSET = 6'h 0;
  parameter logic [BlockAw-1:0] IDMA_REG64_FRONTEND_DST_ADDR_OFFSET = 6'h 8;
  parameter logic [BlockAw-1:0] IDMA_REG64_FRONTEND_NUM_BYTES_OFFSET = 6'h 10;
  parameter logic [BlockAw-1:0] IDMA_REG64_FRONTEND_CONF_OFFSET = 6'h 18;
  parameter logic [BlockAw-1:0] IDMA_REG64_FRONTEND_STATUS_OFFSET = 6'h 20;
  parameter logic [BlockAw-1:0] IDMA_REG64_FRONTEND_NEXT_ID_OFFSET = 6'h 28;
  parameter logic [BlockAw-1:0] IDMA_REG64_FRONTEND_DONE_OFFSET = 6'h 30;

  // Reset values for hwext registers and their fields
  parameter logic [0:0] IDMA_REG64_FRONTEND_STATUS_RESVAL = 1'h 0;
  parameter logic [63:0] IDMA_REG64_FRONTEND_NEXT_ID_RESVAL = 64'h 0;
  parameter logic [63:0] IDMA_REG64_FRONTEND_DONE_RESVAL = 64'h 0;

  // Register index
  typedef enum int {
    IDMA_REG64_FRONTEND_SRC_ADDR,
    IDMA_REG64_FRONTEND_DST_ADDR,
    IDMA_REG64_FRONTEND_NUM_BYTES,
    IDMA_REG64_FRONTEND_CONF,
    IDMA_REG64_FRONTEND_STATUS,
    IDMA_REG64_FRONTEND_NEXT_ID,
    IDMA_REG64_FRONTEND_DONE
  } idma_reg64_frontend_id_e;

  // Register width information to check illegal writes
  parameter logic [3:0] IDMA_REG64_FRONTEND_PERMIT [7] = '{
    4'b 1111, // index[0] IDMA_REG64_FRONTEND_SRC_ADDR
    4'b 1111, // index[1] IDMA_REG64_FRONTEND_DST_ADDR
    4'b 1111, // index[2] IDMA_REG64_FRONTEND_NUM_BYTES
    4'b 0001, // index[3] IDMA_REG64_FRONTEND_CONF
    4'b 0001, // index[4] IDMA_REG64_FRONTEND_STATUS
    4'b 1111, // index[5] IDMA_REG64_FRONTEND_NEXT_ID
    4'b 1111  // index[6] IDMA_REG64_FRONTEND_DONE
  };

endpackage

package dm;
  localparam logic [3:0] DbgVersion013 = 4'h2;
  // size of program buffer in junks of 32-bit words
  localparam logic [4:0] ProgBufSize   = 5'h8;

  // amount of data count registers implemented
  localparam logic [3:0] DataCount     = 4'h2;

  // address to which a hart should jump when it was requested to halt
  localparam logic [63:0] HaltAddress = 64'h800;
  localparam logic [63:0] ResumeAddress = HaltAddress + 4;
  localparam logic [63:0] ExceptionAddress = HaltAddress + 8;

  // address where data0-15 is shadowed or if shadowed in a CSR
  // address of the first CSR used for shadowing the data
  localparam logic [11:0] DataAddr = 12'h380; // we are aligned with Rocket here

  // debug registers
  typedef enum logic [7:0] {
    Data0        = 8'h04,
    Data1        = 8'h05,
    Data2        = 8'h06,
    Data3        = 8'h07,
    Data4        = 8'h08,
    Data5        = 8'h09,
    Data6        = 8'h0A,
    Data7        = 8'h0B,
    Data8        = 8'h0C,
    Data9        = 8'h0D,
    Data10       = 8'h0E,
    Data11       = 8'h0F,
    DMControl    = 8'h10,
    DMStatus     = 8'h11, // r/o
    Hartinfo     = 8'h12,
    HaltSum1     = 8'h13,
    HAWindowSel  = 8'h14,
    HAWindow     = 8'h15,
    AbstractCS   = 8'h16,
    Command      = 8'h17,
    AbstractAuto = 8'h18,
    DevTreeAddr0 = 8'h19,
    DevTreeAddr1 = 8'h1A,
    DevTreeAddr2 = 8'h1B,
    DevTreeAddr3 = 8'h1C,
    NextDM       = 8'h1D,
    ProgBuf0     = 8'h20,
    ProgBuf1     = 8'h21,
    ProgBuf2     = 8'h22,
    ProgBuf3     = 8'h23,
    ProgBuf4     = 8'h24,
    ProgBuf5     = 8'h25,
    ProgBuf6     = 8'h26,
    ProgBuf7     = 8'h27,
    ProgBuf8     = 8'h28,
    ProgBuf9     = 8'h29,
    ProgBuf10    = 8'h2A,
    ProgBuf11    = 8'h2B,
    ProgBuf12    = 8'h2C,
    ProgBuf13    = 8'h2D,
    ProgBuf14    = 8'h2E,
    ProgBuf15    = 8'h2F,
    AuthData     = 8'h30,
    HaltSum2     = 8'h34,
    HaltSum3     = 8'h35,
    SBAddress3   = 8'h37,
    SBCS         = 8'h38,
    SBAddress0   = 8'h39,
    SBAddress1   = 8'h3A,
    SBAddress2   = 8'h3B,
    SBData0      = 8'h3C,
    SBData1      = 8'h3D,
    SBData2      = 8'h3E,
    SBData3      = 8'h3F,
    HaltSum0     = 8'h40
  } dm_csr_e;

  // debug causes
  localparam logic [2:0] CauseBreakpoint = 3'h1;
  localparam logic [2:0] CauseTrigger    = 3'h2;
  localparam logic [2:0] CauseRequest    = 3'h3;
  localparam logic [2:0] CauseSingleStep = 3'h4;

  typedef struct packed {
    logic [31:23] zero1;
    logic         impebreak;
    logic [21:20] zero0;
    logic         allhavereset;
    logic         anyhavereset;
    logic         allresumeack;
    logic         anyresumeack;
    logic         allnonexistent;
    logic         anynonexistent;
    logic         allunavail;
    logic         anyunavail;
    logic         allrunning;
    logic         anyrunning;
    logic         allhalted;
    logic         anyhalted;
    logic         authenticated;
    logic         authbusy;
    logic         hasresethaltreq;
    logic         devtreevalid;
    logic [3:0]   version;
  } dmstatus_t;

  typedef struct packed {
    logic         haltreq;
    logic         resumereq;
    logic         hartreset;
    logic         ackhavereset;
    logic         zero1;
    logic         hasel;
    logic [25:16] hartsello;
    logic [15:6]  hartselhi;
    logic [5:4]   zero0;
    logic         setresethaltreq;
    logic         clrresethaltreq;
    logic         ndmreset;
    logic         dmactive;
  } dmcontrol_t;

  typedef struct packed {
    logic [31:24] zero1;
    logic [23:20] nscratch;
    logic [19:17] zero0;
    logic         dataaccess;
    logic [15:12] datasize;
    logic [11:0]  dataaddr;
  } hartinfo_t;

  typedef enum logic [2:0] {
    CmdErrNone, CmdErrBusy, CmdErrNotSupported,
    CmdErrorException, CmdErrorHaltResume,
    CmdErrorBus, CmdErrorOther = 7
  } cmderr_e;

  typedef struct packed {
    logic [31:29] zero3;
    logic [28:24] progbufsize;
    logic [23:13] zero2;
    logic         busy;
    logic         zero1;
    cmderr_e      cmderr;
    logic [7:4]   zero0;
    logic [3:0]   datacount;
  } abstractcs_t;

  typedef enum logic [7:0] {
    AccessRegister = 8'h0,
    QuickAccess    = 8'h1,
    AccessMemory   = 8'h2
  } cmd_e;

  typedef struct packed {
    cmd_e        cmdtype;
    logic [23:0] control;
  } command_t;

  typedef struct packed {
    logic [31:16] autoexecprogbuf;
    logic [15:12] zero0;
    logic [11:0]  autoexecdata;
  } abstractauto_t;

  typedef struct packed {
    logic         zero1;
    logic [22:20] aarsize;
    logic         aarpostincrement;
    logic         postexec;
    logic         transfer;
    logic         write;
    logic [15:0]  regno;
  } ac_ar_cmd_t;

  // DTM
  typedef enum logic [1:0] {
    DTM_NOP   = 2'h0,
    DTM_READ  = 2'h1,
    DTM_WRITE = 2'h2
  } dtm_op_e;

  typedef enum logic [1:0] {
    DTM_SUCCESS = 2'h0,
    DTM_ERR     = 2'h2,
    DTM_BUSY    = 2'h3
  } dtm_op_status_e;

  typedef struct packed {
    logic [31:29] sbversion;
    logic [28:23] zero0;
    logic         sbbusyerror;
    logic         sbbusy;
    logic         sbreadonaddr;
    logic [19:17] sbaccess;
    logic         sbautoincrement;
    logic         sbreadondata;
    logic [14:12] sberror;
    logic [11:5]  sbasize;
    logic         sbaccess128;
    logic         sbaccess64;
    logic         sbaccess32;
    logic         sbaccess16;
    logic         sbaccess8;
  } sbcs_t;

  typedef struct packed {
    logic [6:0]  addr;
    dtm_op_e     op;
    logic [31:0] data;
  } dmi_req_t;

  typedef struct packed  {
    logic [31:0] data;
    logic [1:0]  resp;
  } dmi_resp_t;

  typedef struct packed {
    logic [31:18] zero1;
    logic         dmihardreset;
    logic         dmireset;
    logic         zero0;
    logic [14:12] idle;
    logic [11:10] dmistat;
    logic [9:4]   abits;
    logic [3:0]   version;
  } dtmcs_t;

  // privilege levels
  typedef enum logic[1:0] {
    PRIV_LVL_M = 2'b11,
    PRIV_LVL_S = 2'b01,
    PRIV_LVL_U = 2'b00
  } priv_lvl_t;

  // debugregs in core
  typedef struct packed {
    logic [31:28]     xdebugver;
    logic [27:16]     zero2;
    logic             ebreakm;
    logic             zero1;
    logic             ebreaks;
    logic             ebreaku;
    logic             stepie;
    logic             stopcount;
    logic             stoptime;
    logic [8:6]       cause;
    logic             zero0;
    logic             mprven;
    logic             nmip;
    logic             step;
    priv_lvl_t        prv;
  } dcsr_t;

  // CSRs
  typedef enum logic [11:0] {
    // Floating-Point CSRs
    CSR_FFLAGS         = 12'h001,
    CSR_FRM            = 12'h002,
    CSR_FCSR           = 12'h003,
    CSR_FTRAN          = 12'h800,
    // Supervisor Mode CSRs
    CSR_SSTATUS        = 12'h100,
    CSR_SIE            = 12'h104,
    CSR_STVEC          = 12'h105,
    CSR_SCOUNTEREN     = 12'h106,
    CSR_SSCRATCH       = 12'h140,
    CSR_SEPC           = 12'h141,
    CSR_SCAUSE         = 12'h142,
    CSR_STVAL          = 12'h143,
    CSR_SIP            = 12'h144,
    CSR_SATP           = 12'h180,
    // Machine Mode CSRs
    CSR_MSTATUS        = 12'h300,
    CSR_MISA           = 12'h301,
    CSR_MEDELEG        = 12'h302,
    CSR_MIDELEG        = 12'h303,
    CSR_MIE            = 12'h304,
    CSR_MTVEC          = 12'h305,
    CSR_MCOUNTEREN     = 12'h306,
    CSR_MSCRATCH       = 12'h340,
    CSR_MEPC           = 12'h341,
    CSR_MCAUSE         = 12'h342,
    CSR_MTVAL          = 12'h343,
    CSR_MIP            = 12'h344,
    CSR_PMPCFG0        = 12'h3A0,
    CSR_PMPADDR0       = 12'h3B0,
    CSR_MVENDORID      = 12'hF11,
    CSR_MARCHID        = 12'hF12,
    CSR_MIMPID         = 12'hF13,
    CSR_MHARTID        = 12'hF14,
    CSR_MCYCLE         = 12'hB00,
    CSR_MINSTRET       = 12'hB02,
    CSR_DCACHE         = 12'h701,
    CSR_ICACHE         = 12'h700,

    CSR_TSELECT        = 12'h7A0,
    CSR_TDATA1         = 12'h7A1,
    CSR_TDATA2         = 12'h7A2,
    CSR_TDATA3         = 12'h7A3,
    CSR_TINFO          = 12'h7A4,

    // Debug CSR
    CSR_DCSR           = 12'h7b0,
    CSR_DPC            = 12'h7b1,
    CSR_DSCRATCH0      = 12'h7b2, // optional
    CSR_DSCRATCH1      = 12'h7b3, // optional

    // Counters and Timers
    CSR_CYCLE          = 12'hC00,
    CSR_TIME           = 12'hC01,
    CSR_INSTRET        = 12'hC02
  } csr_reg_t;

  // SBA state
  typedef enum logic [2:0] {
    Idle,
    Read,
    Write,
    WaitRead,
    WaitWrite
  } sba_state_e;

  // Instruction Generation Helpers
  function automatic logic [31:0] jal (logic [4:0]  rd,
                                       logic [20:0] imm);
    // OpCode Jal
    return {imm[20], imm[10:1], imm[11], imm[19:12], rd, 7'h6f};
  endfunction

  function automatic logic [31:0] jalr (logic [4:0]  rd,
                                        logic [4:0]  rs1,
                                        logic [11:0] offset);
    // OpCode Jal
    return {offset[11:0], rs1, 3'b0, rd, 7'h67};
  endfunction

  function automatic logic [31:0] andi (logic [4:0]  rd,
                                        logic [4:0]  rs1,
                                        logic [11:0] imm);
    // OpCode andi
    return {imm[11:0], rs1, 3'h7, rd, 7'h13};
  endfunction

  function automatic logic [31:0] slli (logic [4:0] rd,
                                        logic [4:0] rs1,
                                        logic [5:0] shamt);
    // OpCode slli
    return {6'b0, shamt[5:0], rs1, 3'h1, rd, 7'h13};
  endfunction

  function automatic logic [31:0] srli (logic [4:0] rd,
                                        logic [4:0] rs1,
                                        logic [5:0] shamt);
    // OpCode srli
    return {6'b0, shamt[5:0], rs1, 3'h5, rd, 7'h13};
  endfunction

  function automatic logic [31:0] load (logic [2:0]  size,
                                        logic [4:0]  dest,
                                        logic [4:0]  base,
                                        logic [11:0] offset);
    // OpCode Load
    return {offset[11:0], base, size, dest, 7'h03};
  endfunction

  function automatic logic [31:0] auipc (logic [4:0]  rd,
                                         logic [20:0] imm);
    // OpCode Auipc
    return {imm[20], imm[10:1], imm[11], imm[19:12], rd, 7'h17};
  endfunction

  function automatic logic [31:0] store (logic [2:0]  size,
                                         logic [4:0]  src,
                                         logic [4:0]  base,
                                         logic [11:0] offset);
    // OpCode Store
    return {offset[11:5], src, base, size, offset[4:0], 7'h23};
  endfunction

  function automatic logic [31:0] float_load (logic [2:0]  size,
                                              logic [4:0]  dest,
                                              logic [4:0]  base,
                                              logic [11:0] offset);
    // OpCode Load
    return {offset[11:0], base, size, dest, 7'b00_001_11};
  endfunction

  function automatic logic [31:0] float_store (logic [2:0]  size,
                                               logic [4:0]  src,
                                               logic [4:0]  base,
                                               logic [11:0] offset);
    // OpCode Store
    return {offset[11:5], src, base, size, offset[4:0], 7'b01_001_11};
  endfunction

  function automatic logic [31:0] csrw (csr_reg_t   csr,
                                        logic [4:0] rs1);
    // CSRRW, rd, OpCode System
    return {csr, rs1, 3'h1, 5'h0, 7'h73};
  endfunction

  function automatic logic [31:0] csrr (csr_reg_t   csr,
                                        logic [4:0] dest);
    // rs1, CSRRS, rd, OpCode System
    return {csr, 5'h0, 3'h2, dest, 7'h73};
  endfunction

  function automatic logic [31:0] branch(logic [4:0]  src2,
                                         logic [4:0]  src1,
                                         logic [2:0]  funct3,
                                         logic [11:0] offset);
    // OpCode Branch
    return {offset[11], offset[9:4], src2, src1, funct3,
        offset[3:0], offset[10], 7'b11_000_11};
  endfunction

  function automatic logic [31:0] ebreak ();
    return 32'h00100073;
  endfunction

  function automatic logic [31:0] wfi ();
    return 32'h10500073;
  endfunction

  function automatic logic [31:0] nop ();
    return 32'h00000013;
  endfunction

  function automatic logic [31:0] illegal ();
    return 32'h00000000;
  endfunction

endpackage : dm
// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Thomas Benz <tbenz@ethz.ch>

`include "axi/typedef.svh"

// for now this is an extended copy of the axi_pkg
// eventually the DMA specific parts should be moved in axi_pkg aswell
package axi_dma_pkg;

  typedef struct packed {
      logic [63:0] aw_stall_cnt, ar_stall_cnt, r_stall_cnt, w_stall_cnt,
                   buf_w_stall_cnt, buf_r_stall_cnt;
      logic [63:0] aw_valid_cnt, aw_ready_cnt, aw_done_cnt, aw_bw;
      logic [63:0] ar_valid_cnt, ar_ready_cnt, ar_done_cnt, ar_bw;
      logic [63:0]  r_valid_cnt,  r_ready_cnt,  r_done_cnt,  r_bw;
      logic [63:0]  w_valid_cnt,  w_ready_cnt,  w_done_cnt,  w_bw;
      logic [63:0]  b_valid_cnt,  b_ready_cnt,  b_done_cnt;
      logic [63:0] next_id,       completed_id;
      logic [63:0] dma_busy_cnt;
  } dma_perf_t;

endpackage
// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Package containing common req resp definitions.
package reqrsp_pkg;

  /// Size field. Same semantic as AXI.
  typedef logic [2:0] size_t;

  typedef enum logic [3:0] {
      AMONone = 4'h0,
      AMOSwap = 4'h1,
      AMOAdd  = 4'h2,
      AMOAnd  = 4'h3,
      AMOOr   = 4'h4,
      AMOXor  = 4'h5,
      AMOMax  = 4'h6,
      AMOMaxu = 4'h7,
      AMOMin  = 4'h8,
      AMOMinu = 4'h9,
      AMOLR   = 4'hA,
      AMOSC   = 4'hB
  } amo_op_e;

  /// The given operation falls into the atomic fetch-and-op memory operations.
  function automatic logic is_amo(amo_op_e amo);
    if (amo inside {AMOSwap, AMOAdd, AMOAnd, AMOOr, AMOXor, AMOMax, AMOMaxu, AMOMin, AMOMinu}) begin
      return 1;
    end else begin
      return 0;
    end
  endfunction

  /// Translate to AXI5+ATOP AMOs
  function automatic logic [5:0] to_axi_amo(amo_op_e amo);
    logic [5:0] result;
    unique case (amo)
      AMOSwap: result = axi_pkg::ATOP_ATOMICSWAP;
      AMOAdd: result = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_ADD};
      // Careful, this case needs to invert the bits on the write data bus.
      AMOAnd: result = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_CLR};
      AMOOr: result = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_SET};
      AMOXor: result = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_EOR};
      AMOMax: result = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_SMAX};
      AMOMaxu: result = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_UMAX};
      AMOMin: result = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_SMIN};
      AMOMinu: result = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_UMIN};
      default: result = '0;
    endcase
    return result;
  endfunction

  /// Translate from AXI5+ATOP AMOs
  function automatic amo_op_e from_axi_amo(axi_pkg::atop_t amo);
    amo_op_e result;
    unique case (amo)
      axi_pkg::ATOP_ATOMICSWAP: result = AMOSwap;
      {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_ADD}: result = AMOAdd;
      // Careful, this case needs to invert the bits on the write data bus.
      {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_CLR}: result = AMOAnd;
      {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_SET}: result = AMOOr;
      {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_EOR}: result = AMOXor;
      {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_SMAX}: result = AMOMax;
      {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_UMAX}: result = AMOMaxu;
      {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_SMIN}: result = AMOMin;
      {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_UMIN}: result = AMOMinu;
      default: result = AMONone;
    endcase
    return result;
  endfunction
endpackage
// Copyright (c) 2014-2020 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// - Matheus Cavalcante <matheusd@iis.ee.ethz.ch>

//! AXI Package
/// Contains all necessary type definitions, constants, and generally useful functions.

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Register Package auto-generated by `reggen` containing data structure

package snitch_cluster_peripheral_reg_pkg;

  // Param list
  parameter int NumPerfCounters = 16;

  // Address widths within the block
  parameter int BlockAw = 9;

  ////////////////////////////
  // Typedefs for registers //
  ////////////////////////////

  typedef struct packed {
    struct packed {
      logic        q;
    } cycle;
    struct packed {
      logic        q;
    } tcdm_accessed;
    struct packed {
      logic        q;
    } tcdm_congested;
    struct packed {
      logic        q;
    } issue_fpu;
    struct packed {
      logic        q;
    } issue_fpu_seq;
    struct packed {
      logic        q;
    } issue_core_to_fpu;
    struct packed {
      logic        q;
    } retired_instr;
    struct packed {
      logic        q;
    } retired_load;
    struct packed {
      logic        q;
    } retired_i;
    struct packed {
      logic        q;
    } retired_acc;
    struct packed {
      logic        q;
    } dma_aw_stall;
    struct packed {
      logic        q;
    } dma_ar_stall;
    struct packed {
      logic        q;
    } dma_r_stall;
    struct packed {
      logic        q;
    } dma_w_stall;
    struct packed {
      logic        q;
    } dma_buf_w_stall;
    struct packed {
      logic        q;
    } dma_buf_r_stall;
    struct packed {
      logic        q;
    } dma_aw_done;
    struct packed {
      logic        q;
    } dma_aw_bw;
    struct packed {
      logic        q;
    } dma_ar_done;
    struct packed {
      logic        q;
    } dma_ar_bw;
    struct packed {
      logic        q;
    } dma_r_done;
    struct packed {
      logic        q;
    } dma_r_bw;
    struct packed {
      logic        q;
    } dma_w_done;
    struct packed {
      logic        q;
    } dma_w_bw;
    struct packed {
      logic        q;
    } dma_b_done;
    struct packed {
      logic        q;
    } dma_busy;
    struct packed {
      logic        q;
    } icache_miss;
    struct packed {
      logic        q;
    } icache_hit;
    struct packed {
      logic        q;
    } icache_prefetch;
    struct packed {
      logic        q;
    } icache_double_hit;
    struct packed {
      logic        q;
    } icache_stall;
  } snitch_cluster_peripheral_reg2hw_perf_counter_enable_mreg_t;

  typedef struct packed {
    logic [9:0] q;
  } snitch_cluster_peripheral_reg2hw_hart_select_mreg_t;

  typedef struct packed {
    logic [47:0] q;
    logic        qe;
  } snitch_cluster_peripheral_reg2hw_perf_counter_mreg_t;

  typedef struct packed {
    logic [31:0] q;
    logic        qe;
  } snitch_cluster_peripheral_reg2hw_cl_clint_set_reg_t;

  typedef struct packed {
    logic [31:0] q;
    logic        qe;
  } snitch_cluster_peripheral_reg2hw_cl_clint_clear_reg_t;

  typedef struct packed {
    logic [31:0] q;
  } snitch_cluster_peripheral_reg2hw_hw_barrier_reg_t;

  typedef struct packed {
    logic        q;
  } snitch_cluster_peripheral_reg2hw_icache_prefetch_enable_reg_t;

  typedef struct packed {
    logic [47:0] d;
  } snitch_cluster_peripheral_hw2reg_perf_counter_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } snitch_cluster_peripheral_hw2reg_hw_barrier_reg_t;

  // Register -> HW type
  typedef struct packed {
    snitch_cluster_peripheral_reg2hw_perf_counter_enable_mreg_t [15:0] perf_counter_enable; // [1538:1043]
    snitch_cluster_peripheral_reg2hw_hart_select_mreg_t [15:0] hart_select; // [1042:883]
    snitch_cluster_peripheral_reg2hw_perf_counter_mreg_t [15:0] perf_counter; // [882:99]
    snitch_cluster_peripheral_reg2hw_cl_clint_set_reg_t cl_clint_set; // [98:66]
    snitch_cluster_peripheral_reg2hw_cl_clint_clear_reg_t cl_clint_clear; // [65:33]
    snitch_cluster_peripheral_reg2hw_hw_barrier_reg_t hw_barrier; // [32:1]
    snitch_cluster_peripheral_reg2hw_icache_prefetch_enable_reg_t icache_prefetch_enable; // [0:0]
  } snitch_cluster_peripheral_reg2hw_t;

  // HW -> register type
  typedef struct packed {
    snitch_cluster_peripheral_hw2reg_perf_counter_mreg_t [15:0] perf_counter; // [799:32]
    snitch_cluster_peripheral_hw2reg_hw_barrier_reg_t hw_barrier; // [31:0]
  } snitch_cluster_peripheral_hw2reg_t;

  // Register offsets
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_0_OFFSET = 9'h 0;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_1_OFFSET = 9'h 8;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_2_OFFSET = 9'h 10;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_3_OFFSET = 9'h 18;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_4_OFFSET = 9'h 20;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_5_OFFSET = 9'h 28;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_6_OFFSET = 9'h 30;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_7_OFFSET = 9'h 38;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_8_OFFSET = 9'h 40;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_9_OFFSET = 9'h 48;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_10_OFFSET = 9'h 50;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_11_OFFSET = 9'h 58;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_12_OFFSET = 9'h 60;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_13_OFFSET = 9'h 68;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_14_OFFSET = 9'h 70;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_15_OFFSET = 9'h 78;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_0_OFFSET = 9'h 80;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_1_OFFSET = 9'h 88;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_2_OFFSET = 9'h 90;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_3_OFFSET = 9'h 98;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_4_OFFSET = 9'h a0;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_5_OFFSET = 9'h a8;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_6_OFFSET = 9'h b0;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_7_OFFSET = 9'h b8;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_8_OFFSET = 9'h c0;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_9_OFFSET = 9'h c8;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_10_OFFSET = 9'h d0;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_11_OFFSET = 9'h d8;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_12_OFFSET = 9'h e0;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_13_OFFSET = 9'h e8;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_14_OFFSET = 9'h f0;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_15_OFFSET = 9'h f8;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_0_OFFSET = 9'h 100;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_1_OFFSET = 9'h 108;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_2_OFFSET = 9'h 110;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_3_OFFSET = 9'h 118;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_4_OFFSET = 9'h 120;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_5_OFFSET = 9'h 128;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_6_OFFSET = 9'h 130;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_7_OFFSET = 9'h 138;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_8_OFFSET = 9'h 140;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_9_OFFSET = 9'h 148;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_10_OFFSET = 9'h 150;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_11_OFFSET = 9'h 158;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_12_OFFSET = 9'h 160;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_13_OFFSET = 9'h 168;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_14_OFFSET = 9'h 170;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_15_OFFSET = 9'h 178;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_CL_CLINT_SET_OFFSET = 9'h 180;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_CL_CLINT_CLEAR_OFFSET = 9'h 188;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_HW_BARRIER_OFFSET = 9'h 190;
  parameter logic [BlockAw-1:0] SNITCH_CLUSTER_PERIPHERAL_ICACHE_PREFETCH_ENABLE_OFFSET = 9'h 198;

  // Reset values for hwext registers and their fields
  parameter logic [47:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_0_RESVAL = 48'h 0;
  parameter logic [47:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_1_RESVAL = 48'h 0;
  parameter logic [47:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_2_RESVAL = 48'h 0;
  parameter logic [47:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_3_RESVAL = 48'h 0;
  parameter logic [47:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_4_RESVAL = 48'h 0;
  parameter logic [47:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_5_RESVAL = 48'h 0;
  parameter logic [47:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_6_RESVAL = 48'h 0;
  parameter logic [47:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_7_RESVAL = 48'h 0;
  parameter logic [47:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_8_RESVAL = 48'h 0;
  parameter logic [47:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_9_RESVAL = 48'h 0;
  parameter logic [47:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_10_RESVAL = 48'h 0;
  parameter logic [47:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_11_RESVAL = 48'h 0;
  parameter logic [47:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_12_RESVAL = 48'h 0;
  parameter logic [47:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_13_RESVAL = 48'h 0;
  parameter logic [47:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_14_RESVAL = 48'h 0;
  parameter logic [47:0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_15_RESVAL = 48'h 0;
  parameter logic [31:0] SNITCH_CLUSTER_PERIPHERAL_CL_CLINT_SET_RESVAL = 32'h 0;
  parameter logic [31:0] SNITCH_CLUSTER_PERIPHERAL_CL_CLINT_CLEAR_RESVAL = 32'h 0;
  parameter logic [31:0] SNITCH_CLUSTER_PERIPHERAL_HW_BARRIER_RESVAL = 32'h 0;

  // Register index
  typedef enum int {
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_0,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_1,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_2,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_3,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_4,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_5,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_6,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_7,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_8,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_9,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_10,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_11,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_12,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_13,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_14,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_15,
    SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_0,
    SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_1,
    SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_2,
    SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_3,
    SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_4,
    SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_5,
    SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_6,
    SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_7,
    SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_8,
    SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_9,
    SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_10,
    SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_11,
    SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_12,
    SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_13,
    SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_14,
    SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_15,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_0,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_1,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_2,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_3,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_4,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_5,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_6,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_7,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_8,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_9,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_10,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_11,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_12,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_13,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_14,
    SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_15,
    SNITCH_CLUSTER_PERIPHERAL_CL_CLINT_SET,
    SNITCH_CLUSTER_PERIPHERAL_CL_CLINT_CLEAR,
    SNITCH_CLUSTER_PERIPHERAL_HW_BARRIER,
    SNITCH_CLUSTER_PERIPHERAL_ICACHE_PREFETCH_ENABLE
  } snitch_cluster_peripheral_id_e;

  // Register width information to check illegal writes
  parameter logic [3:0] SNITCH_CLUSTER_PERIPHERAL_PERMIT [52] = '{
    4'b 1111, // index[ 0] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_0
    4'b 1111, // index[ 1] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_1
    4'b 1111, // index[ 2] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_2
    4'b 1111, // index[ 3] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_3
    4'b 1111, // index[ 4] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_4
    4'b 1111, // index[ 5] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_5
    4'b 1111, // index[ 6] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_6
    4'b 1111, // index[ 7] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_7
    4'b 1111, // index[ 8] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_8
    4'b 1111, // index[ 9] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_9
    4'b 1111, // index[10] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_10
    4'b 1111, // index[11] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_11
    4'b 1111, // index[12] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_12
    4'b 1111, // index[13] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_13
    4'b 1111, // index[14] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_14
    4'b 1111, // index[15] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_ENABLE_15
    4'b 0011, // index[16] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_0
    4'b 0011, // index[17] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_1
    4'b 0011, // index[18] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_2
    4'b 0011, // index[19] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_3
    4'b 0011, // index[20] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_4
    4'b 0011, // index[21] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_5
    4'b 0011, // index[22] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_6
    4'b 0011, // index[23] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_7
    4'b 0011, // index[24] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_8
    4'b 0011, // index[25] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_9
    4'b 0011, // index[26] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_10
    4'b 0011, // index[27] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_11
    4'b 0011, // index[28] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_12
    4'b 0011, // index[29] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_13
    4'b 0011, // index[30] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_14
    4'b 0011, // index[31] SNITCH_CLUSTER_PERIPHERAL_HART_SELECT_15
    4'b 1111, // index[32] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_0
    4'b 1111, // index[33] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_1
    4'b 1111, // index[34] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_2
    4'b 1111, // index[35] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_3
    4'b 1111, // index[36] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_4
    4'b 1111, // index[37] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_5
    4'b 1111, // index[38] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_6
    4'b 1111, // index[39] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_7
    4'b 1111, // index[40] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_8
    4'b 1111, // index[41] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_9
    4'b 1111, // index[42] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_10
    4'b 1111, // index[43] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_11
    4'b 1111, // index[44] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_12
    4'b 1111, // index[45] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_13
    4'b 1111, // index[46] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_14
    4'b 1111, // index[47] SNITCH_CLUSTER_PERIPHERAL_PERF_COUNTER_15
    4'b 1111, // index[48] SNITCH_CLUSTER_PERIPHERAL_CL_CLINT_SET
    4'b 1111, // index[49] SNITCH_CLUSTER_PERIPHERAL_CL_CLINT_CLEAR
    4'b 1111, // index[50] SNITCH_CLUSTER_PERIPHERAL_HW_BARRIER
    4'b 0001  // index[51] SNITCH_CLUSTER_PERIPHERAL_ICACHE_PREFETCH_ENABLE
  };

endpackage

// Copyright (c) 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@ethz.ch>

/// Package with the struct definition for the seeds and an example.
package cb_filter_pkg;
  typedef struct packed {
    int unsigned PermuteSeed;
    int unsigned XorSeed;
  } cb_seed_t;

  // example seeding struct
  localparam cb_seed_t [2:0] EgSeeds = '{
    '{PermuteSeed: 32'd299034753, XorSeed: 32'd4094834  },
    '{PermuteSeed: 32'd19921030,  XorSeed: 32'd995713   },
    '{PermuteSeed: 32'd294388,    XorSeed: 32'd65146511 }
  };
endpackage
// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

package snitch_icache_pkg;

    typedef struct packed {
      logic l0_miss;
      logic l0_hit;
      logic l0_prefetch;
      logic l0_double_hit;
      logic l0_stall;
    } icache_events_t;

    typedef struct packed {
        // Parameters passed to the root module.
        int NR_FETCH_PORTS;
        int LINE_WIDTH;
        int LINE_COUNT;
        int SET_COUNT;
        int PENDING_COUNT;
        int L0_LINE_COUNT;
        int FETCH_AW;
        int FETCH_DW;
        int FILL_AW;
        int FILL_DW;
        bit EARLY_LATCH;
        bit BUFFER_LOOKUP;
        bit GUARANTEE_ORDERING;

        // Derived values.
        int FETCH_ALIGN;
        int FILL_ALIGN;
        int LINE_ALIGN;
        int COUNT_ALIGN;
        int SET_ALIGN;
        int TAG_WIDTH;
        int L0_TAG_WIDTH;
        int L0_EARLY_TAG_WIDTH;
        int ID_WIDTH_REQ;
        int ID_WIDTH_RESP;
        int PENDING_IW; // refill ID width
    } config_t;

endpackage
//-----------------------------------------------------------------------------
// Copyright (C) 2022 ETH Zurich, University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// SPDX-License-Identifier: SHL-0.51
//-----------------------------------------------------------------------------
//
// Author: Manuel Eggimann <meggimann@iis.ee.ethz.ch>
//
// Contains common defintions for the CDC Clear Synchronization Circuitry

package cdc_reset_ctrlr_pkg;

typedef enum logic[1:0] {
  CLEAR_PHASE_IDLE,
  CLEAR_PHASE_ISOLATE,
  CLEAR_PHASE_CLEAR,
  CLEAR_PHASE_POST_CLEAR
} clear_seq_phase_e;

endpackage : cdc_reset_ctrlr_pkg
// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

package snitch_ipu_pkg;

  // IPU
  typedef enum integer {
    RV32BNone,
    RV32BBalanced,
    RV32BFull
  } rv32b_e;

  typedef enum logic [5:0] {
    // Arithmetics
    ALU_ADD,
    ALU_SUB,

    // Logics
    ALU_XOR,
    ALU_OR,
    ALU_AND,
    // RV32B
    ALU_XNOR,
    ALU_ORN,
    ALU_ANDN,

    // Shifts
    ALU_SRA,
    ALU_SRL,
    ALU_SLL,
    // RV32B
    ALU_SRO,
    ALU_SLO,
    ALU_ROR,
    ALU_ROL,
    ALU_GREV,
    ALU_GORC,
    ALU_SHFL,
    ALU_UNSHFL,

    // Comparisons
    ALU_LT,
    ALU_LTU,
    ALU_GE,
    ALU_GEU,
    ALU_EQ,
    ALU_NE,
    // RV32B
    ALU_MIN,
    ALU_MINU,
    ALU_MAX,
    ALU_MAXU,

    // Pack
    // RV32B
    ALU_PACK,
    ALU_PACKU,
    ALU_PACKH,

    // Sign-Extend
    // RV32B
    ALU_SEXTB,
    ALU_SEXTH,

    // Bitcounting
    // RV32B
    ALU_CLZ,
    ALU_CTZ,
    ALU_PCNT,

    // Set lower than
    ALU_SLT,
    ALU_SLTU,

    // Ternary Bitmanip Operations
    // RV32B
    ALU_CMOV,
    ALU_CMIX,
    ALU_FSL,
    ALU_FSR,

    // Single-Bit Operations
    // RV32B
    ALU_SBSET,
    ALU_SBCLR,
    ALU_SBINV,
    ALU_SBEXT,

    // Bit Extract / Deposit
    // RV32B
    ALU_BEXT,
    ALU_BDEP,

    // Bit Field Place
    // RV32B
    ALU_BFP,

    // Carry-less Multiply
    // RV32B
    ALU_CLMUL,
    ALU_CLMULR,
    ALU_CLMULH,

    // Cyclic Redundancy Check
    ALU_CRC32_B,
    ALU_CRC32C_B,
    ALU_CRC32_H,
    ALU_CRC32C_H,
    ALU_CRC32_W,
    ALU_CRC32C_W
  } alu_op_e;

endpackage
// Copyright 2016 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/// cf_math_pkg: Constant Function Implementations of Mathematical Functions for HDL Elaboration
///
/// This package contains a collection of mathematical functions that are commonly used when defining
/// the value of constants in HDL code.  These functions are implemented as Verilog constants
/// functions.  Introduced in Verilog 2001 (IEEE Std 1364-2001), a constant function (§ 10.3.5) is a
/// function whose value can be evaluated at compile time or during elaboration.  A constant function
/// must be called with arguments that are constants.
package cf_math_pkg;

    /// Ceiled Division of Two Natural Numbers
    ///
    /// Returns the quotient of two natural numbers, rounded towards plus infinity.
    function automatic integer ceil_div (input longint dividend, input longint divisor);
        automatic longint remainder;

        // pragma translate_off
        `ifndef VERILATOR
        if (dividend < 0) begin
            $fatal(1, "Dividend %0d is not a natural number!", dividend);
        end

        if (divisor < 0) begin
            $fatal(1, "Divisor %0d is not a natural number!", divisor);
        end

        if (divisor == 0) begin
            $fatal(1, "Division by zero!");
        end
        `endif
        // pragma translate_on

        remainder = dividend;
        for (ceil_div = 0; remainder > 0; ceil_div++) begin
            remainder = remainder - divisor;
        end
    endfunction

    /// Index width required to be able to represent up to `num_idx` indices as a binary
    /// encoded signal.
    /// Ensures that the minimum width if an index signal is `1`, regardless of parametrization.
    ///
    /// Sample usage in type definition:
    /// As parameter:
    ///   `parameter type idx_t = logic[cf_math_pkg::idx_width(NumIdx)-1:0]`
    /// As typedef:
    ///   `typedef logic [cf_math_pkg::idx_width(NumIdx)-1:0] idx_t`
    function automatic integer unsigned idx_width (input integer unsigned num_idx);
        return (num_idx > 32'd1) ? unsigned'($clog2(num_idx)) : 32'd1;
    endfunction

endpackage
// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// # Snitch-wide Constants.
/// Fixed constants for a Snitch system.

package snitch_pkg;

  localparam dm::hartinfo_t SnitchHartinfo = '{
    zero1: '0,
    nscratch: 1,
    zero0: '0,
    dataaccess: 1,
    datasize: dm::DataCount,
    dataaddr: dm::DataAddr
  };

  /// Async interrupts of the core.
  typedef struct packed {
    /// Debug request
    logic debug;
    /// Machine external interrupt pending
    logic meip;
    /// Machine external timer interrupt pending
    logic mtip;
    /// Machine external software interrupt pending
    logic msip;
    /// Machine cluster-local interrupt pending
    logic mcip;
  } interrupts_t;

  typedef enum logic [31:0] {
    FP_SS = 0,
    SHARED_MULDIV = 1,
    DMA_SS = 2,
    INT_SS = 3,
    SSR_CFG = 4
  } acc_addr_e;

  typedef enum logic [1:0] {
    PrivLvlM = 2'b11,
    PrivLvlS = 2'b01,
    PrivLvlU = 2'b00
  } priv_lvl_t;

  // Extension state.
  typedef enum logic [1:0] {
    XOff = 2'b00,
    XInitial = 2'b01,
    XClean = 2'b10,
    XDirty = 2'b11
  } x_state_e;

  typedef struct packed {
    logic         sd;     // signal dirty - read-only - hardwired zero
    logic [7:0]   wpri3;  // writes preserved reads ignored
    logic         tsr;    // trap sret
    logic         tw;     // time wait
    logic         tvm;    // trap virtual memory
    logic         mxr;    // make executable readable
    logic         sum;    // permit supervisor user memory access
    logic         mprv;   // modify privilege - privilege level for ld/st
    x_state_e     xs;     // extension register - hardwired to zero
    x_state_e     fs;     // extension register - hardwired to zero for non FP and to Dirty for FP.
    priv_lvl_t    mpp;    // holds the previous privilege mode up to machine
    logic [1:0]   wpri2;  // writes preserved reads ignored
    logic         spp;    // holds the previous privilege mode up to supervisor
    logic         mpie;   // machine interrupts enable bit active prior to trap
    logic         wpri1;  // writes preserved reads ignored
    logic         spie;   // supervisor interrupts enable bit active prior to trap
    logic         upie;   // user interrupts enable bit active prior to trap - hardwired to zero
    logic         mie;    // machine interrupts enable
    logic         wpri0;  // writes preserved reads ignored
    logic         sie;    // supervisor interrupts enable
    logic         uie;    // user interrupts enable - hardwired to zero
  } status_rv32_t;

  // Virtual Memory
  localparam int unsigned PAGE_SHIFT = 12;
  /// Size in bits of the virtual address segments
  localparam int unsigned VPN_SIZE = 10;

  /// Virtual Address Definition
  typedef struct packed {
    /// Virtual Page Number 1
    logic [31:32-VPN_SIZE] vpn1;
    /// Virtual Page Number 0
    logic [PAGE_SHIFT+VPN_SIZE-1:PAGE_SHIFT] vpn0;
  } va_t;

  typedef struct packed {
    logic               d;
    logic               a;
    logic               u;
    logic               x;
    logic               w;
    logic               r;
  } pte_flags_t;

  localparam logic [3:0] INSTR_ADDR_MISALIGNED = 0;
  localparam logic [3:0] INSTR_ACCESS_FAULT    = 1;
  localparam logic [3:0] ILLEGAL_INSTR         = 2;
  localparam logic [3:0] BREAKPOINT            = 3;
  localparam logic [3:0] LD_ADDR_MISALIGNED    = 4;
  localparam logic [3:0] LD_ACCESS_FAULT       = 5;
  localparam logic [3:0] ST_ADDR_MISALIGNED    = 6;
  localparam logic [3:0] ST_ACCESS_FAULT       = 7;
  localparam logic [3:0] ENV_CALL_UMODE        = 8;  // environment call from user mode
  localparam logic [3:0] ENV_CALL_SMODE        = 9;  // environment call from supervisor mode
  localparam logic [3:0] ENV_CALL_MMODE        = 11; // environment call from machine mode
  localparam logic [3:0] INSTR_PAGE_FAULT      = 12; // Instruction page fault
  localparam logic [3:0] LOAD_PAGE_FAULT       = 13; // Load page fault
  localparam logic [3:0] STORE_PAGE_FAULT      = 15; // Store page fault

  localparam logic [3:0] MSI = 3;
  localparam logic [3:0] MTI = 7;
  localparam logic [3:0] MEI = 11;
  localparam logic [4:0] MCI = 19;
  localparam logic [3:0] SSI = 1;
  localparam logic [3:0] STI = 5;
  localparam logic [3:0] SEI = 9;
  localparam logic [4:0] SCI = 17;

  // Slaves on Cluster AXI Bus
  typedef enum integer {
    TCDM               = 0,
    ClusterPeripherals = 1,
    SoC                = 2
  } cluster_slave_e;

  typedef enum integer {
    CoreReq = 0,
    AXISoC  = 1,
    PTW     = 2
  } cluster_master_e;

  // Slaves on Cluster DMA AXI Bus
  typedef enum int unsigned {
    TCDMDMA    = 0,
    SoCDMAOut  = 1,
    ZeroMemory = 2
  } cluster_slave_dma_e;

  typedef enum int unsigned {
    SDMAMst  = 32'd0,
    SoCDMAIn = 32'd1,
    ICache   = 32'd2
  } cluster_master_dma_e;

  /// Possible interconnect implementations.
  typedef enum bit {
    /// Crossbar implementation. We call it `LogarithmicInterconnect` because the
    /// response path isn't arbitrated.
    LogarithmicInterconnect,
    /// Omega Network. It is isomorphic to a butterfly network.
    OmegaNet
  } topo_e;

  // Event strobes per core, counted by the performance counters in the cluster
  // peripherals.
  typedef struct packed {
    logic issue_fpu;          // core operations performed in the FPU
    logic issue_fpu_seq;      // includes load/store operations
    logic issue_core_to_fpu;  // instructions issued from core to FPU
    logic retired_instr;      // number of instructions retired by the core
    logic retired_load;       // number of load instructions retired by the core
    logic retired_i;          // number of base instructions retired by the core
    logic retired_acc;        // number of offloaded instructions retired by the core
  } core_events_t;

  // SSRs
  localparam logic [11:0] CSR_MSEG = 12'hBC0;

  // --------------------
  // Trace Infrastructure
  // --------------------
  // pragma translate_off
  typedef enum logic [1:0] {
    SrcSnitch =  0,
    SrcFpu = 1,
    SrcFpuSeq = 2
  } trace_src_e;

  typedef struct packed {
    longint source;
    longint stall;
    longint exception;
    longint rs1;
    longint rs2;
    longint rd;
    longint is_load;
    longint is_store;
    longint is_branch;
    longint pc_d;
    longint opa;
    longint opb;
    longint opa_select;
    longint opb_select;
    longint write_rd;
    longint csr_addr;
    longint writeback;
    longint gpr_rdata_1;
    longint ls_size;
    longint ld_result_32;
    longint lsu_rd;
    longint retire_load;
    longint alu_result;
    longint ls_amo;
    longint retire_acc;
    longint acc_pid;
    longint acc_pdata_32;
    longint fpu_offload;
    longint is_seq_insn;
  } snitch_trace_port_t;

  function automatic string print_snitch_trace(snitch_trace_port_t snitch_trace);
    string extras_str = "{";
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "source", snitch_trace.source);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "stall", snitch_trace.stall);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "exception", snitch_trace.exception);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "rs1", snitch_trace.rs1);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "rs2", snitch_trace.rs2);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "rd", snitch_trace.rd);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "is_load", snitch_trace.is_load);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "is_store", snitch_trace.is_store);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "is_branch", snitch_trace.is_branch);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "pc_d", snitch_trace.pc_d);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "opa", snitch_trace.opa);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "opb", snitch_trace.opb);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "opa_select", snitch_trace.opa_select);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "opb_select", snitch_trace.opb_select);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "write_rd", snitch_trace.write_rd);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "csr_addr", snitch_trace.csr_addr);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "writeback", snitch_trace.writeback);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "gpr_rdata_1", snitch_trace.gpr_rdata_1);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "ls_size", snitch_trace.ls_size);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "ld_result_32", snitch_trace.ld_result_32);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "lsu_rd", snitch_trace.lsu_rd);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "retire_load", snitch_trace.retire_load);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "alu_result", snitch_trace.alu_result);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "ls_amo", snitch_trace.ls_amo);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "retire_acc", snitch_trace.retire_acc);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "acc_pid", snitch_trace.acc_pid);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "acc_pdata_32", snitch_trace.acc_pdata_32);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "fpu_offload", snitch_trace.fpu_offload);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "is_seq_insn", snitch_trace.is_seq_insn);
    extras_str = $sformatf("%s}", extras_str);
    return extras_str;
  endfunction

  // Trace-Port Definitions
  typedef struct packed {
    longint source;
    longint acc_q_hs;
    longint fpu_out_hs;
    longint lsu_q_hs;
    longint op_in;
    longint rs1;
    longint rs2;
    longint rs3;
    longint rd;
    longint op_sel_0;
    longint op_sel_1;
    longint op_sel_2;
    longint src_fmt;
    longint dst_fmt;
    longint int_fmt;
    longint acc_qdata_0;
    longint acc_qdata_1;
    longint acc_qdata_2;
    longint op_0;
    longint op_1;
    longint op_2;
    longint use_fpu;
    longint fpu_in_rd;
    longint fpu_in_acc;
    longint ls_size;
    longint is_load;
    longint is_store;
    longint lsu_qaddr;
    longint lsu_rd;
    longint acc_wb_ready;
    longint fpu_out_acc;
    longint fpr_waddr;
    longint fpr_wdata;
    longint fpr_we;
  } fpu_trace_port_t;

  function automatic string print_fpu_trace(fpu_trace_port_t fpu_trace);
    string extras_str = "{";
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "source", fpu_trace.source);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "acc_q_hs", fpu_trace.acc_q_hs);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "fpu_out_hs", fpu_trace.fpu_out_hs);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "lsu_q_hs", fpu_trace.lsu_q_hs);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "op_in", fpu_trace.op_in);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "rs1", fpu_trace.rs1);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "rs2", fpu_trace.rs2);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "rs3", fpu_trace.rs3);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "rd", fpu_trace.rd);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "op_sel_0", fpu_trace.op_sel_0);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "op_sel_1", fpu_trace.op_sel_1);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "op_sel_2", fpu_trace.op_sel_2);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "src_fmt", fpu_trace.src_fmt);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "dst_fmt", fpu_trace.dst_fmt);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "int_fmt", fpu_trace.int_fmt);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "acc_qdata_0", fpu_trace.acc_qdata_0);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "acc_qdata_1", fpu_trace.acc_qdata_1);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "acc_qdata_2", fpu_trace.acc_qdata_2);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "op_0", fpu_trace.op_0);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "op_1", fpu_trace.op_1);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "op_2", fpu_trace.op_2);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "use_fpu", fpu_trace.use_fpu);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "fpu_in_rd", fpu_trace.fpu_in_rd);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "fpu_in_acc", fpu_trace.fpu_in_acc);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "ls_size", fpu_trace.ls_size);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "is_load", fpu_trace.is_load);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "is_store", fpu_trace.is_store);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "lsu_qaddr", fpu_trace.lsu_qaddr);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "lsu_rd", fpu_trace.lsu_rd);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "acc_wb_ready", fpu_trace.acc_wb_ready);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "fpu_out_acc", fpu_trace.fpu_out_acc);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "fpr_waddr", fpu_trace.fpr_waddr);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "fpr_wdata", fpu_trace.fpr_wdata);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "fpr_we", fpu_trace.fpr_we);
    extras_str = $sformatf("%s}", extras_str);
    return extras_str;
  endfunction

  typedef struct packed {
    longint source;
    longint cbuf_push;
    longint is_outer;
    longint max_inst;
    longint max_rpt;
    longint stg_max;
    longint stg_mask;
  } fpu_sequencer_trace_port_t;

  function automatic string print_fpu_sequencer_trace(fpu_sequencer_trace_port_t fpu_sequencer);
    string extras_str = "{";
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "source", fpu_sequencer.source);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "cbuf_push", fpu_sequencer.cbuf_push);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "is_outer", fpu_sequencer.is_outer);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "max_inst", fpu_sequencer.max_inst);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "max_rpt", fpu_sequencer.max_rpt);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "stg_max", fpu_sequencer.stg_max);
    extras_str = $sformatf("%s'%s': 0x%0x, ", extras_str, "stg_mask", fpu_sequencer.stg_mask);
    extras_str = $sformatf("%s}", extras_str);
    return extras_str;
  endfunction
  // pragma translate_on

endpackage
/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:   dm_pkg.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   30.6.2018
 *
 * Description: Debug-module package, contains common system definitions.
 *
 */

// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

// Description: PMA Checks for Snitch.
package snitch_pma_pkg;

  localparam int unsigned NrMaxRules = 4;

  typedef struct packed {
      logic [47:0] base; // base which needs to match
      logic [47:0] mask; // bit mask which bits to consider when matching the rule
  } rule_t;

  typedef struct packed {
    // PMAs
    // Non-idempotent regions
    int unsigned            NrNonIdempotentRegionRules; // Number of non-idempotent rules
    rule_t [NrMaxRules-1:0] NonIdempotentRegion;
    // Execute Regions
    int unsigned            NrExecuteRegionRules; // Number of regions which have execute property
    rule_t [NrMaxRules-1:0] ExecuteRegion;
    // Cached Regions
    int unsigned            NrCachedRegionRules; // Number of regions which have cached property
    rule_t [NrMaxRules-1:0] CachedRegion;
    // Atomicity Regions
    int unsigned            NrAMORegionRules; // Number of regions which have Atomic property
    rule_t [NrMaxRules-1:0] AMORegion;
  } snitch_pma_t;

  // Public interface
  function automatic logic range_check(logic[47:0] base, logic[47:0] mask, logic[47:0] address);
    return (address & mask) == (base & mask);
  endfunction : range_check

  function automatic logic is_inside_nonidempotent_regions (snitch_pma_t cfg, logic[47:0] address);
    logic [NrMaxRules-1:0] pass;
    pass = '0;
    for (int unsigned k = 0; k < cfg.NrNonIdempotentRegionRules; k++) begin
      pass[k] =
        range_check(cfg.NonIdempotentRegion[k].base, cfg.NonIdempotentRegion[k].mask, address);
    end
    return |pass;
  endfunction : is_inside_nonidempotent_regions

  function automatic logic is_inside_execute_regions (snitch_pma_t cfg, logic[47:0] address);
    // if we don't specify any region we assume everything is accessible
    logic [NrMaxRules-1:0] pass;
    pass = '0;
    for (int unsigned k = 0; k < cfg.NrExecuteRegionRules; k++) begin
      pass[k] = range_check(cfg.ExecuteRegion[k].base, cfg.ExecuteRegion[k].mask, address);
    end
    return |pass;
  endfunction : is_inside_execute_regions

  function automatic logic is_inside_cacheable_regions (snitch_pma_t cfg, logic[47:0] address);
    automatic logic [NrMaxRules-1:0] pass;
    pass = '0;
    for (int unsigned k = 0; k < cfg.NrCachedRegionRules; k++) begin
      pass[k] = range_check(cfg.CachedRegion[k].base, cfg.CachedRegion[k].mask, address);
    end
    return |pass;
  endfunction : is_inside_cacheable_regions
endpackage
// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
//
/// Contains common ECC definitions and helper functions.

package ecc_pkg;

  // Calculate required ECC parity width:
  function automatic int unsigned get_parity_width (input int unsigned data_width);
    // data_width + cw_width + 1 <= 2**cw_width
    int unsigned cw_width = 2;
    while (unsigned'(2**cw_width) < cw_width + data_width + 1) cw_width++;
    return cw_width;
  endfunction

  // Calculate required ECC codeword width:
  function automatic int unsigned get_cw_width (input int unsigned data_width);
    // data width + parity width + one additional parity bit (for double error detection)
    return data_width + get_parity_width(data_width);
  endfunction

endpackage
// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Paul Scheffler <paulsc@iis.ee.ethz.ch>

// Types and fixed constants for SSRs.

package snitch_ssr_pkg;

  // Passed parameters for individual SSRs
  typedef struct packed {
    bit           Indirection;
    bit           IsectMaster;
    bit           IsectMasterIdx;
    bit           IsectSlave;
    bit           IsectSlaveSpill;
    bit           IndirOutSpill;
    int unsigned  NumLoops;
    int unsigned  IndexWidth;
    int unsigned  PointerWidth;
    int unsigned  ShiftWidth;
    int unsigned  RptWidth;
    int unsigned  IndexCredits;
    int unsigned  IsectSlaveCredits;
    int unsigned  DataCredits;
    int unsigned  MuxRespDepth;
  } ssr_cfg_t;

  // Derived parameters for intersection
  typedef struct packed {
    int unsigned  IndexWidth;
    int unsigned  NumMaster0;
    int unsigned  NumMaster1;
    int unsigned  NumSlave;
    int unsigned  IdxMaster0;
    int unsigned  IdxMaster1;
    int unsigned  IdxSlave;
    int unsigned  StreamctlDepth;
  } isect_cfg_t;

  // Fields used in addresses of upper alias registers
  // *Not* the same order as alias address, but as in upper status fields
  typedef struct packed {
    logic no_indir;
    logic write;
    logic [1:0] dims;
  } cfg_alias_fields_t;

  // Upper fields accessible on status register
  typedef struct packed {
    logic done;
    logic write;
    logic [1:0] dims;
    logic indir;
  } cfg_status_upper_t;

  // Indexing control flags
  typedef struct packed {
    logic merge;
  } idx_flags_t;

  // Layout of indexing control register
  typedef struct packed {
    idx_flags_t flags;
    logic [7:0] shift;
    logic [7:0] size;
  } cfg_idx_ctl_t;

endpackage
// Copyright 2019 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// SPDX-License-Identifier: SHL-0.51

// Author: Stefan Mach <smach@iis.ee.ethz.ch>

package fpnew_pkg;

  // ---------
  // FP TYPES
  // ---------
  // | Enumerator | Format           | Width  | EXP_BITS | MAN_BITS
  // |:----------:|------------------|-------:|:--------:|:--------:
  // | FP32       | IEEE binary32    | 32 bit | 8        | 23
  // | FP64       | IEEE binary64    | 64 bit | 11       | 52
  // | FP16       | IEEE binary16    | 16 bit | 5        | 10
  // | FP8        | binary8          |  8 bit | 5        | 2
  // | FP16ALT    | binary16alt      | 16 bit | 8        | 7
  // | FP8ALT     | binary8alt       |  8 bit | 4        | 3
  // *NOTE:* Add new formats only at the end of the enumeration for backwards compatibilty!

  // Encoding for a format
  typedef struct packed {
    int unsigned exp_bits;
    int unsigned man_bits;
  } fp_encoding_t;

  localparam int unsigned NUM_FP_FORMATS = 6; // change me to add formats
  localparam int unsigned FP_FORMAT_BITS = $clog2(NUM_FP_FORMATS);

  // FP formats
  typedef enum logic [FP_FORMAT_BITS-1:0] {
    FP32    = 'd0,
    FP64    = 'd1,
    FP16    = 'd2,
    FP8     = 'd3,
    FP16ALT = 'd4,
    FP8ALT  = 'd5
    // add new formats here
  } fp_format_e;

  // Encodings for supported FP formats
  localparam fp_encoding_t [0:NUM_FP_FORMATS-1] FP_ENCODINGS  = '{
    '{8,  23}, // IEEE binary32 (single)
    '{11, 52}, // IEEE binary64 (double)
    '{5,  10}, // IEEE binary16 (half)
    '{5,  2},  // custom binary8
    '{8,  7},  // custom binary16alt
    '{4,  3}   // custom binary8alt
    // add new formats here
  };

  typedef logic [0:NUM_FP_FORMATS-1]       fmt_logic_t;    // Logic indexed by FP format (for masks)
  typedef logic [0:NUM_FP_FORMATS-1][31:0] fmt_unsigned_t; // Unsigned indexed by FP format

  localparam fmt_logic_t CPK_FORMATS  = 6'b110000; // FP32 and FP64 can provide CPK only
  // FP32, FP64 cannot be provided for DOTP
  // Small hack: FP32 only enabled for wide enough wrapper input widths for vsum.s instruction
  localparam fmt_logic_t DOTP_FORMATS = 6'b101111;

  // ---------
  // INT TYPES
  // ---------
  // | Enumerator | Width  |
  // |:----------:|-------:|
  // | INT8       |  8 bit |
  // | INT16      | 16 bit |
  // | INT32      | 32 bit |
  // | INT64      | 64 bit |
  // *NOTE:* Add new formats only at the end of the enumeration for backwards compatibilty!

  localparam int unsigned NUM_INT_FORMATS = 4; // change me to add formats
  localparam int unsigned INT_FORMAT_BITS = $clog2(NUM_INT_FORMATS);

  // Int formats
  typedef enum logic [INT_FORMAT_BITS-1:0] {
    INT8,
    INT16,
    INT32,
    INT64
    // add new formats here
  } int_format_e;

  // Returns the width of an INT format by index
  function automatic int unsigned int_width(int_format_e ifmt);
    unique case (ifmt)
      INT8:  return 8;
      INT16: return 16;
      INT32: return 32;
      INT64: return 64;
      default: begin
        // pragma translate_off
        $fatal(1, "Invalid INT format supplied");
        // pragma translate_on
        // just return any integer to avoid any latches
        // hopefully this error is caught by simulation
        return INT8;
      end
    endcase
  endfunction

  typedef logic [0:NUM_INT_FORMATS-1] ifmt_logic_t; // Logic indexed by INT format (for masks)

  // --------------
  // FP OPERATIONS
  // --------------
  localparam int unsigned NUM_OPGROUPS = 5;

  // Each FP operation belongs to an operation group
  typedef enum logic [2:0] {
    ADDMUL, DIVSQRT, NONCOMP, CONV, DOTP
  } opgroup_e;

  localparam int unsigned OP_BITS = 5;

  typedef enum logic [OP_BITS-1:0] {
    SDOTP, EXVSUM, VSUM,         // DOTP operation group
    FMADD, FNMSUB, ADD, MUL,     // ADDMUL operation group
    DIV, SQRT,                   // DIVSQRT operation group
    SGNJ, MINMAX, CMP, CLASSIFY, // NONCOMP operation group
    F2F, F2I, I2F, CPKAB, CPKCD  // CONV operation group
  } operation_e;

  // -------------------
  // RISC-V FP-SPECIFIC
  // -------------------
  // Rounding modes
  typedef enum logic [2:0] {
    RNE = 3'b000,
    RTZ = 3'b001,
    RDN = 3'b010,
    RUP = 3'b011,
    RMM = 3'b100,
    DYN = 3'b111
  } roundmode_e;

  // Status flags
  typedef struct packed {
    logic NV; // Invalid
    logic DZ; // Divide by zero
    logic OF; // Overflow
    logic UF; // Underflow
    logic NX; // Inexact
  } status_t;

  // CSR encoded alternate fp formats
  typedef struct packed {
    logic src; // Source format selection
    logic dst; // Destination format selection
  } fmt_mode_t;

  // Information about a floating point value
  typedef struct packed {
    logic is_normal;     // is the value normal
    logic is_subnormal;  // is the value subnormal
    logic is_zero;       // is the value zero
    logic is_inf;        // is the value infinity
    logic is_nan;        // is the value NaN
    logic is_signalling; // is the value a signalling NaN
    logic is_quiet;      // is the value a quiet NaN
    logic is_boxed;      // is the value properly NaN-boxed (RISC-V specific)
  } fp_info_t;

  // Classification mask
  typedef enum logic [9:0] {
    NEGINF     = 10'b00_0000_0001,
    NEGNORM    = 10'b00_0000_0010,
    NEGSUBNORM = 10'b00_0000_0100,
    NEGZERO    = 10'b00_0000_1000,
    POSZERO    = 10'b00_0001_0000,
    POSSUBNORM = 10'b00_0010_0000,
    POSNORM    = 10'b00_0100_0000,
    POSINF     = 10'b00_1000_0000,
    SNAN       = 10'b01_0000_0000,
    QNAN       = 10'b10_0000_0000
  } classmask_e;

  // ------------------
  // FPU configuration
  // ------------------
  // Pipelining registers can be inserted (at elaboration time) into operational units
  typedef enum logic [1:0] {
    BEFORE,     // registers are inserted at the inputs of the unit
    AFTER,      // registers are inserted at the outputs of the unit
    INSIDE,     // registers are inserted at predetermined (suboptimal) locations in the unit
    DISTRIBUTED // registers are evenly distributed, INSIDE >= AFTER >= BEFORE
  } pipe_config_t;

  // Arithmetic units can be arranged in parallel (per format), merged (multi-format) or not at all.
  typedef enum logic [1:0] {
    DISABLED, // arithmetic units are not generated
    PARALLEL, // arithmetic units are generated in prallel slices, one for each format
    MERGED    // arithmetic units are contained within a merged unit holding multiple formats
  } unit_type_t;

  // Array of unit types indexed by format
  typedef unit_type_t [0:NUM_FP_FORMATS-1] fmt_unit_types_t;

  // Array of format-specific unit types by opgroup
  typedef fmt_unit_types_t [0:NUM_OPGROUPS-1] opgrp_fmt_unit_types_t;
  // same with unsigned
  typedef fmt_unsigned_t [0:NUM_OPGROUPS-1] opgrp_fmt_unsigned_t;

  // FPU configuration: features
  typedef struct packed {
    int unsigned Width;
    logic        EnableVectors;
    logic        EnableNanBox;
    fmt_logic_t  FpFmtMask;
    ifmt_logic_t IntFmtMask;
  } fpu_features_t;

  localparam fpu_features_t RV64D = '{
    Width:         64,
    EnableVectors: 1'b0,
    EnableNanBox:  1'b1,
    FpFmtMask:     6'b110000,
    IntFmtMask:    4'b0011
  };

  localparam fpu_features_t RV32D = '{
    Width:         64,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     6'b110000,
    IntFmtMask:    4'b0010
  };

  localparam fpu_features_t RV32F = '{
    Width:         32,
    EnableVectors: 1'b0,
    EnableNanBox:  1'b1,
    FpFmtMask:     6'b100000,
    IntFmtMask:    4'b0010
  };

  localparam fpu_features_t RV64D_Xsflt = '{
    Width:         64,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     6'b111111,
    IntFmtMask:    4'b1111
  };

  localparam fpu_features_t RV32F_Xsflt = '{
    Width:         32,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     6'b101111,
    IntFmtMask:    4'b1110
  };

  localparam fpu_features_t RV32F_Xf16alt_Xfvec = '{
    Width:         32,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     6'b100010,
    IntFmtMask:    4'b0110
  };


  // FPU configuraion: implementation
  typedef struct packed {
    opgrp_fmt_unsigned_t   PipeRegs;
    opgrp_fmt_unit_types_t UnitTypes;
    pipe_config_t          PipeConfig;
  } fpu_implementation_t;

  localparam fpu_implementation_t DEFAULT_NOREGS = '{
    PipeRegs:   '{default: 0},
    UnitTypes:  '{'{default: PARALLEL}, // ADDMUL
                  '{default: MERGED},   // DIVSQRT
                  '{default: PARALLEL}, // NONCOMP
                  '{default: MERGED},   // CONV
                  '{default: MERGED}},  // DOTP
    PipeConfig: BEFORE
  };

  localparam fpu_implementation_t DEFAULT_SNITCH = '{
    PipeRegs:   '{default: 1},
    UnitTypes:  '{'{default: PARALLEL}, // ADDMUL
                  '{default: DISABLED}, // DIVSQRT
                  '{default: PARALLEL}, // NONCOMP
                  '{default: MERGED},   // CONV
                  '{default: MERGED}},  // DOTP
    PipeConfig: BEFORE
  };

  // -----------------------
  // Synthesis optimization
  // -----------------------
  localparam logic DONT_CARE = 1'b1; // the value to assign as don't care

  // -------------------------
  // General helper functions
  // -------------------------
  function automatic int minimum(int a, int b);
    return (a < b) ? a : b;
  endfunction

  function automatic int maximum(int a, int b);
    return (a > b) ? a : b;
  endfunction

  // -------------------------------------------
  // Helper functions for FP formats and values
  // -------------------------------------------
  // Returns the width of a FP format
  function automatic int unsigned fp_width(fp_format_e fmt);
    return FP_ENCODINGS[fmt].exp_bits + FP_ENCODINGS[fmt].man_bits + 1;
  endfunction

  // Returns the widest FP format present
  function automatic int unsigned max_fp_width(fmt_logic_t cfg);
    automatic int unsigned res = 0;
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i])
        res = unsigned'(maximum(res, fp_width(fp_format_e'(i))));
    return res;
  endfunction


  function automatic int unsigned max_dotp_dst_fp_width(fmt_logic_t cfg);
    automatic int unsigned res = 0;
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i])
        res = unsigned'(maximum(res, fp_format_e'(i)));
    return res;
  endfunction

  // Returns the narrowest FP format present
  function automatic int unsigned min_fp_width(fmt_logic_t cfg);
    automatic int unsigned res = max_fp_width(cfg);
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i])
        res = unsigned'(minimum(res, fp_width(fp_format_e'(i))));
    return res;
  endfunction

  // Returns the number of expoent bits for a format
  function automatic int unsigned exp_bits(fp_format_e fmt);
    return FP_ENCODINGS[fmt].exp_bits;
  endfunction

  // Returns the number of mantissa bits for a format
  function automatic int unsigned man_bits(fp_format_e fmt);
    return FP_ENCODINGS[fmt].man_bits;
  endfunction

  // Returns the bias value for a given format (as per IEEE 754-2008)
  function automatic int unsigned bias(fp_format_e fmt);
    return unsigned'(2**(FP_ENCODINGS[fmt].exp_bits-1)-1); // symmetrical bias
  endfunction

  function automatic fp_encoding_t super_format(fmt_logic_t cfg);
    automatic fp_encoding_t res;
    res = '0;
    for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
      if (cfg[fmt]) begin // only active format
        res.exp_bits = unsigned'(maximum(res.exp_bits, exp_bits(fp_format_e'(fmt))));
        res.man_bits = unsigned'(maximum(res.man_bits, man_bits(fp_format_e'(fmt))));
      end
    return res;
  endfunction

  function automatic fp_format_e expanded_format(fp_format_e input_format);
    automatic fp_format_e res;
    case (input_format)
      FP32    : res = FP64;
      FP64    : res = FP64;
      FP16    : res = FP32;
      FP8     : res = FP16;
      FP16ALT : res = FP32;
      FP8ALT  : res = FP16;
      default : res = FP64;
    endcase
    return res;
  endfunction

  // -------------------------------------------
  // Helper functions for INT formats and values
  // -------------------------------------------
  // Returns the widest INT format present
  function automatic int unsigned max_int_width(ifmt_logic_t cfg);
    automatic int unsigned res = 0;
    for (int ifmt = 0; ifmt < NUM_INT_FORMATS; ifmt++) begin
      if (cfg[ifmt]) res = maximum(res, int_width(int_format_e'(ifmt)));
    end
    return res;
  endfunction

  // --------------------------------------------------
  // Helper functions for operations and FPU structure
  // --------------------------------------------------
  // Returns the operation group of the given operation
  function automatic opgroup_e get_opgroup(operation_e op);
    unique case (op)
      FMADD, FNMSUB, ADD, MUL:     return ADDMUL;
      DIV, SQRT:                   return DIVSQRT;
      SGNJ, MINMAX, CMP, CLASSIFY: return NONCOMP;
      F2F, F2I, I2F, CPKAB, CPKCD: return CONV;
      SDOTP, EXVSUM, VSUM:         return DOTP;
      default:                     return NONCOMP;
    endcase
  endfunction

  // Returns the number of operands by operation group
  function automatic int unsigned num_operands(opgroup_e grp);
    unique case (grp)
      ADDMUL:  return 3;
      DIVSQRT: return 2;
      NONCOMP: return 2;
      CONV:    return 3; // vectorial casts use 3 operands
      DOTP:    return 3; // splitting into 5 operands done in wrapper
      default: return 0;
    endcase
  endfunction

  // Returns the number of lanes according to width, format and vectors
  function automatic int unsigned num_lanes(int unsigned width, fp_format_e fmt, logic vec);
    return vec ? width / fp_width(fmt) : 1; // if no vectors, only one lane
  endfunction

  // Returns the maximum number of lanes in the FPU according to width, format config and vectors
  function automatic int unsigned max_num_lanes(int unsigned width, fmt_logic_t cfg, logic vec);
    return vec ? width / min_fp_width(cfg) : 1; // if no vectors, only one lane
  endfunction

  // Returns a mask of active FP formats that are present in lane lane_no of a multiformat slice
  function automatic fmt_logic_t get_lane_formats(int unsigned width,
                                                  fmt_logic_t cfg,
                                                  int unsigned lane_no);
    automatic fmt_logic_t res;
    for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
      // Mask active formats with the number of lanes for that format
      res[fmt] = cfg[fmt] & (width / fp_width(fp_format_e'(fmt)) > lane_no);
    return res;
  endfunction

  // Returns a mask of active INT formats that are present in lane lane_no of a multiformat slice
  function automatic ifmt_logic_t get_lane_int_formats(int unsigned width,
                                                       fmt_logic_t cfg,
                                                       ifmt_logic_t icfg,
                                                       int unsigned lane_no);
    automatic ifmt_logic_t res;
    automatic fmt_logic_t lanefmts;
    res = '0;
    lanefmts = get_lane_formats(width, cfg, lane_no);

    for (int unsigned ifmt = 0; ifmt < NUM_INT_FORMATS; ifmt++)
      for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
        // Mask active int formats with the width of the float formats
        if ((fp_width(fp_format_e'(fmt)) == int_width(int_format_e'(ifmt))))
          res[ifmt] |= icfg[ifmt] && lanefmts[fmt];
    return res;
  endfunction

  // Returns a mask of active FP formats that are present in lane lane_no of a CONV slice
  function automatic fmt_logic_t get_conv_lane_formats(int unsigned width,
                                                       fmt_logic_t cfg,
                                                       int unsigned lane_no);
    automatic fmt_logic_t res;
    for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
      // Mask active formats with the number of lanes for that format, CPK at least twice
      res[fmt] = cfg[fmt] && ((width / fp_width(fp_format_e'(fmt)) > lane_no) ||
                             (CPK_FORMATS[fmt] && (lane_no < 2)));
    return res;
  endfunction

  // Returns a mask of active FP formats that are currenlty supported for DOTP operations
  function automatic fmt_logic_t get_dotp_lane_formats(int unsigned width,
                                                       fmt_logic_t cfg,
                                                       int unsigned lane_no);
    automatic fmt_logic_t res;
    for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
      // Mask active formats with the number of lanes for that format, CPK at least twice
      res[fmt] = cfg[fmt] && ((width / (fp_width(fp_format_e'(fmt))*2) > (lane_no/2)) && DOTP_FORMATS[fmt]);
    return res;
  endfunction

  // Returns the dotp dest FP format string
  function automatic fmt_logic_t get_dotp_dst_fmts(fmt_logic_t cfg);
    automatic fmt_logic_t res;
    unique case (cfg) // goes through some of the allowed configurations
      6'b001111:  res=6'b101111; // fp8(alt) -> fp16(alt) & fp16(alt) -> fp32
      6'b000101:  res=6'b001111; // fp8(alt) -> fp16(alt)
      default: return '0;
    endcase
    return res;
  endfunction

  // Returns a mask of active INT formats that are present in lane lane_no of a CONV slice
  function automatic ifmt_logic_t get_conv_lane_int_formats(int unsigned width,
                                                            fmt_logic_t cfg,
                                                            ifmt_logic_t icfg,
                                                            int unsigned lane_no);
    automatic ifmt_logic_t res;
    automatic fmt_logic_t lanefmts;
    res = '0;
    lanefmts = get_conv_lane_formats(width, cfg, lane_no);

    for (int unsigned ifmt = 0; ifmt < NUM_INT_FORMATS; ifmt++)
      for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
        // Mask active int formats with the width of the float formats
        res[ifmt] |= icfg[ifmt] && lanefmts[fmt] &&
                     (fp_width(fp_format_e'(fmt)) == int_width(int_format_e'(ifmt)));
    return res;
  endfunction

  // Return whether any active format is set as MERGED
  function automatic logic any_enabled_multi(fmt_unit_types_t types, fmt_logic_t cfg);
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i] && types[i] == MERGED)
        return 1'b1;
      return 1'b0;
  endfunction

  // Return whether the given format is the first active one set as MERGED
  function automatic logic is_first_enabled_multi(fp_format_e fmt,
                                                  fmt_unit_types_t types,
                                                  fmt_logic_t cfg);
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++) begin
      if (cfg[i] && types[i] == MERGED) return (fp_format_e'(i) == fmt);
    end
    return 1'b0;
  endfunction

  // Returns the first format that is active and is set as MERGED
  function automatic fp_format_e get_first_enabled_multi(fmt_unit_types_t types, fmt_logic_t cfg);
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i] && types[i] == MERGED)
        return fp_format_e'(i);
      return fp_format_e'(0);
  endfunction

  // Returns the largest number of regs that is active and is set as MERGED
  function automatic int unsigned get_num_regs_multi(fmt_unsigned_t regs,
                                                     fmt_unit_types_t types,
                                                     fmt_logic_t cfg);
    automatic int unsigned res = 0;
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++) begin
      if (cfg[i] && types[i] == MERGED) res = maximum(res, regs[i]);
    end
    return res;
  endfunction

endpackage
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

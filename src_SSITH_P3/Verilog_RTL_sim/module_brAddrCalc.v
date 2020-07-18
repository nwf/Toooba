//
// Generated by Bluespec Compiler, version 2019.05.beta2 (build a88bf40db, 2019-05-24)
//
// On Sat Jul 18 16:00:30 BST 2020
//
//
// Ports:
// Name                         I/O  size props
// brAddrCalc                     O   163
// brAddrCalc_pc                  I   163
// brAddrCalc_val                 I   163
// brAddrCalc_iType               I     5
// brAddrCalc_imm                 I    64
// brAddrCalc_taken               I     1
// brAddrCalc_orig_inst           I    32
// brAddrCalc_cap                 I     1
//
// Combinational paths from inputs to outputs:
//   (brAddrCalc_pc,
//    brAddrCalc_val,
//    brAddrCalc_iType,
//    brAddrCalc_imm,
//    brAddrCalc_taken,
//    brAddrCalc_orig_inst,
//    brAddrCalc_cap) -> brAddrCalc
//
//

`ifdef BSV_ASSIGNMENT_DELAY
`else
  `define BSV_ASSIGNMENT_DELAY
`endif

`ifdef BSV_POSITIVE_RESET
  `define BSV_RESET_VALUE 1'b1
  `define BSV_RESET_EDGE posedge
`else
  `define BSV_RESET_VALUE 1'b0
  `define BSV_RESET_EDGE negedge
`endif

module module_brAddrCalc(brAddrCalc_pc,
			 brAddrCalc_val,
			 brAddrCalc_iType,
			 brAddrCalc_imm,
			 brAddrCalc_taken,
			 brAddrCalc_orig_inst,
			 brAddrCalc_cap,
			 brAddrCalc);
  // value method brAddrCalc
  input  [162 : 0] brAddrCalc_pc;
  input  [162 : 0] brAddrCalc_val;
  input  [4 : 0] brAddrCalc_iType;
  input  [63 : 0] brAddrCalc_imm;
  input  brAddrCalc_taken;
  input  [31 : 0] brAddrCalc_orig_inst;
  input  brAddrCalc_cap;
  output [162 : 0] brAddrCalc;

  // signals for module outputs
  wire [162 : 0] brAddrCalc;

  // remaining internal signals
  reg [85 : 0] IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_pc_BI_ETC___d162;
  reg [63 : 0] IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_pc_BI_ETC___d131;
  reg [9 : 0] IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_pc_BI_ETC___d222;
  reg IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_imm_B_ETC___d101;
  wire [85 : 0] _0_CONCAT_IF_brAddrCalc_cap_THEN_brAddrCalc_val_ETC___d154;
  wire [65 : 0] cap_capFat_address__h847,
		pointer__h118,
		pointer__h445,
		pointer__h487,
		pointer__h516,
		result_d_address__h838,
		targetAddr_capFat_address__h460,
		x__h1250,
		x__h1280,
		x__h1311;
  wire [63 : 0] addBase__h1108,
		address__h106,
		address__h480,
		bot__h1111,
		x__h309,
		x__h766,
		x__h940;
  wire [55 : 0] IF_brAddrCalc_cap_THEN_brAddrCalc_val_BIT_65_4_ETC___d153;
  wire [49 : 0] highBitsfilter__h524,
		highOffsetBits__h127,
		highOffsetBits__h525,
		highOffsetBits__h618,
		mask__h1109,
		signBits__h522,
		signBits__h615,
		x__h552,
		x__h645;
  wire [15 : 0] newAddrBits__h827, x__h1165;
  wire [13 : 0] IF_brAddrCalc_iType_EQ_10_7_THEN_IF_brAddrCalc_ETC___d159,
		cap_capFat_addrBits__h848,
		cap_capFat_bounds_baseBits__h872,
		cap_capFat_bounds_topBits__h871,
		repBoundBits__h133,
		repBoundBits__h531,
		result_d_addrBits__h839,
		toBoundsM1__h137,
		toBoundsM1__h535,
		toBoundsM1__h628,
		toBounds__h136,
		toBounds__h534,
		toBounds__h627;
  wire [11 : 0] inc__h105;
  wire [5 : 0] IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_43__ETC___d37;
  wire [4 : 0] IF_brAddrCalc_iType_EQ_10_7_THEN_IF_brAddrCalc_ETC___d218,
	       _0_CONCAT_brAddrCalc_pc_BITS_159_TO_96_22_PLUS__ETC___d216,
	       brAddrCalc_pc_BITS_161_TO_96_02_PLUS_0_CONCAT__ETC___d178;
  wire [3 : 0] IF_IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS__ETC___d202;
  wire [2 : 0] cap_tempFields_repBoundTopBits__h991,
	       repBound__h1615,
	       repBound__h1625;
  wire [1 : 0] jumpTarget_capFat_reserved__h438;
  wire IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_23__ETC___d190,
       IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_37__ETC___d189,
       IF_brAddrCalc_imm_BIT_63_THEN_NOT_brAddrCalc_i_ETC___d24,
       IF_brAddrCalc_imm_BIT_63_THEN_NOT_brAddrCalc_i_ETC___d71,
       IF_brAddrCalc_val_BIT_159_8_THEN_NOT_brAddrCal_ETC___d91,
       NOT_brAddrCalc_pc_BITS_43_TO_38_ULT_50_6___d27,
       _0_CONCAT_IF_brAddrCalc_cap_THEN_brAddrCalc_val_ETC___d192,
       _0_CONCAT_brAddrCalc_pc_BITS_159_TO_96_22_PLUS__ETC___d206,
       brAddrCalc_imm_BITS_63_TO_14_XOR_SEXT_brAddrCa_ETC___d30,
       brAddrCalc_imm_BITS_63_TO_14_XOR_SEXT_brAddrCa_ETC___d96,
       brAddrCalc_pc_BITS_161_TO_96_02_PLUS_0_CONCAT__ETC___d168,
       brAddrCalc_pc_BITS_23_TO_21_4_ULT_brAddrCalc_p_ETC___d166,
       brAddrCalc_pc_BITS_37_TO_35_64_ULT_brAddrCalc__ETC___d165,
       brAddrCalc_val_BITS_159_TO_110_7_XOR_SEXT_brAd_ETC___d94,
       jumpTarget_capFat_flags__h437;

  // value method brAddrCalc
  assign brAddrCalc =
	     { IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_imm_B_ETC___d101,
	       targetAddr_capFat_address__h460,
	       IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_pc_BI_ETC___d162,
	       IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_pc_BI_ETC___d222 } ;

  // remaining internal signals
  assign IF_IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS__ETC___d202 =
	     { (IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_37__ETC___d189 ==
		_0_CONCAT_IF_brAddrCalc_cap_THEN_brAddrCalc_val_ETC___d192) ?
		 2'd0 :
		 ((IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_37__ETC___d189 &&
		   !_0_CONCAT_IF_brAddrCalc_cap_THEN_brAddrCalc_val_ETC___d192) ?
		    2'd1 :
		    2'd3),
	       (IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_23__ETC___d190 ==
		_0_CONCAT_IF_brAddrCalc_cap_THEN_brAddrCalc_val_ETC___d192) ?
		 2'd0 :
		 ((IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_23__ETC___d190 &&
		   !_0_CONCAT_IF_brAddrCalc_cap_THEN_brAddrCalc_val_ETC___d192) ?
		    2'd1 :
		    2'd3) } ;
  assign IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_23__ETC___d190 =
	     cap_capFat_bounds_baseBits__h872[13:11] < repBound__h1615 ;
  assign IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_37__ETC___d189 =
	     cap_capFat_bounds_topBits__h871[13:11] < repBound__h1615 ;
  assign IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_43__ETC___d37 =
	     brAddrCalc_cap ? brAddrCalc_val[43:38] : brAddrCalc_pc[43:38] ;
  assign IF_brAddrCalc_cap_THEN_brAddrCalc_val_BIT_65_4_ETC___d153 =
	     { jumpTarget_capFat_flags__h437,
	       jumpTarget_capFat_reserved__h438,
	       18'd262143,
	       brAddrCalc_cap ?
		 brAddrCalc_val[44:10] :
		 brAddrCalc_pc[44:10] } ;
  assign IF_brAddrCalc_iType_EQ_10_7_THEN_IF_brAddrCalc_ETC___d159 =
	     (brAddrCalc_iType == 5'd10) ?
	       (brAddrCalc_taken ? x__h1250[13:0] : x__h1311[13:0]) :
	       x__h1311[13:0] ;
  assign IF_brAddrCalc_iType_EQ_10_7_THEN_IF_brAddrCalc_ETC___d218 =
	     (brAddrCalc_iType == 5'd10) ?
	       (brAddrCalc_taken ?
		  brAddrCalc_pc_BITS_161_TO_96_02_PLUS_0_CONCAT__ETC___d178 :
		  _0_CONCAT_brAddrCalc_pc_BITS_159_TO_96_22_PLUS__ETC___d216) :
	       _0_CONCAT_brAddrCalc_pc_BITS_159_TO_96_22_PLUS__ETC___d216 ;
  assign IF_brAddrCalc_imm_BIT_63_THEN_NOT_brAddrCalc_i_ETC___d24 =
	     brAddrCalc_imm[63] ?
	       x__h309[13:0] >= toBounds__h136 &&
	       repBoundBits__h133 != brAddrCalc_pc[95:82] :
	       x__h309[13:0] < toBoundsM1__h137 ;
  assign IF_brAddrCalc_imm_BIT_63_THEN_NOT_brAddrCalc_i_ETC___d71 =
	     brAddrCalc_imm[63] ?
	       x__h940[13:0] >= toBounds__h534 &&
	       repBoundBits__h531 != cap_capFat_addrBits__h848 :
	       x__h940[13:0] < toBoundsM1__h535 ;
  assign IF_brAddrCalc_val_BIT_159_8_THEN_NOT_brAddrCal_ETC___d91 =
	     brAddrCalc_val[159] ?
	       x__h766[13:0] >= toBounds__h627 :
	       x__h766[13:0] <= toBoundsM1__h628 ;
  assign NOT_brAddrCalc_pc_BITS_43_TO_38_ULT_50_6___d27 =
	     brAddrCalc_pc[43:38] >= 6'd50 ;
  assign _0_CONCAT_IF_brAddrCalc_cap_THEN_brAddrCalc_val_ETC___d154 =
	     { x__h1280[13:0],
	       brAddrCalc_cap ? brAddrCalc_val[81:66] : brAddrCalc_pc[81:66],
	       IF_brAddrCalc_cap_THEN_brAddrCalc_val_BIT_65_4_ETC___d153 } ;
  assign _0_CONCAT_IF_brAddrCalc_cap_THEN_brAddrCalc_val_ETC___d192 =
	     x__h1280[13:11] < repBound__h1615 ;
  assign _0_CONCAT_brAddrCalc_pc_BITS_159_TO_96_22_PLUS__ETC___d206 =
	     x__h1311[13:11] < repBound__h1625 ;
  assign _0_CONCAT_brAddrCalc_pc_BITS_159_TO_96_22_PLUS__ETC___d216 =
	     { _0_CONCAT_brAddrCalc_pc_BITS_159_TO_96_22_PLUS__ETC___d206,
	       (brAddrCalc_pc_BITS_37_TO_35_64_ULT_brAddrCalc__ETC___d165 ==
		_0_CONCAT_brAddrCalc_pc_BITS_159_TO_96_22_PLUS__ETC___d206) ?
		 2'd0 :
		 ((brAddrCalc_pc_BITS_37_TO_35_64_ULT_brAddrCalc__ETC___d165 &&
		   !_0_CONCAT_brAddrCalc_pc_BITS_159_TO_96_22_PLUS__ETC___d206) ?
		    2'd1 :
		    2'd3),
	       (brAddrCalc_pc_BITS_23_TO_21_4_ULT_brAddrCalc_p_ETC___d166 ==
		_0_CONCAT_brAddrCalc_pc_BITS_159_TO_96_22_PLUS__ETC___d206) ?
		 2'd0 :
		 ((brAddrCalc_pc_BITS_23_TO_21_4_ULT_brAddrCalc_p_ETC___d166 &&
		   !_0_CONCAT_brAddrCalc_pc_BITS_159_TO_96_22_PLUS__ETC___d206) ?
		    2'd1 :
		    2'd3) } ;
  assign addBase__h1108 =
	     { {48{x__h1165[15]}}, x__h1165 } << brAddrCalc_pc[43:38] ;
  assign address__h106 =
	     brAddrCalc_pc[159:96] + { {52{inc__h105[11]}}, inc__h105 } ;
  assign address__h480 = { pointer__h516[63:1], 1'b0 } ;
  assign bot__h1111 =
	     { brAddrCalc_pc[159:110] & mask__h1109, 14'd0 } +
	     addBase__h1108 ;
  assign brAddrCalc_imm_BITS_63_TO_14_XOR_SEXT_brAddrCa_ETC___d30 =
	     (highOffsetBits__h127 == 50'd0 &&
	      IF_brAddrCalc_imm_BIT_63_THEN_NOT_brAddrCalc_i_ETC___d24 ||
	      NOT_brAddrCalc_pc_BITS_43_TO_38_ULT_50_6___d27) &&
	     brAddrCalc_pc[162] ;
  assign brAddrCalc_imm_BITS_63_TO_14_XOR_SEXT_brAddrCa_ETC___d96 =
	     (highOffsetBits__h525 == 50'd0 &&
	      IF_brAddrCalc_imm_BIT_63_THEN_NOT_brAddrCalc_i_ETC___d71 ||
	      IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_43__ETC___d37 >=
	      6'd50) &&
	     (brAddrCalc_cap ?
		brAddrCalc_val[162] :
		brAddrCalc_val_BITS_159_TO_110_7_XOR_SEXT_brAd_ETC___d94) ;
  assign brAddrCalc_pc_BITS_161_TO_96_02_PLUS_0_CONCAT__ETC___d168 =
	     x__h1250[13:11] < repBound__h1625 ;
  assign brAddrCalc_pc_BITS_161_TO_96_02_PLUS_0_CONCAT__ETC___d178 =
	     { brAddrCalc_pc_BITS_161_TO_96_02_PLUS_0_CONCAT__ETC___d168,
	       (brAddrCalc_pc_BITS_37_TO_35_64_ULT_brAddrCalc__ETC___d165 ==
		brAddrCalc_pc_BITS_161_TO_96_02_PLUS_0_CONCAT__ETC___d168) ?
		 2'd0 :
		 ((brAddrCalc_pc_BITS_37_TO_35_64_ULT_brAddrCalc__ETC___d165 &&
		   !brAddrCalc_pc_BITS_161_TO_96_02_PLUS_0_CONCAT__ETC___d168) ?
		    2'd1 :
		    2'd3),
	       (brAddrCalc_pc_BITS_23_TO_21_4_ULT_brAddrCalc_p_ETC___d166 ==
		brAddrCalc_pc_BITS_161_TO_96_02_PLUS_0_CONCAT__ETC___d168) ?
		 2'd0 :
		 ((brAddrCalc_pc_BITS_23_TO_21_4_ULT_brAddrCalc_p_ETC___d166 &&
		   !brAddrCalc_pc_BITS_161_TO_96_02_PLUS_0_CONCAT__ETC___d168) ?
		    2'd1 :
		    2'd3) } ;
  assign brAddrCalc_pc_BITS_23_TO_21_4_ULT_brAddrCalc_p_ETC___d166 =
	     brAddrCalc_pc[23:21] < repBound__h1625 ;
  assign brAddrCalc_pc_BITS_37_TO_35_64_ULT_brAddrCalc__ETC___d165 =
	     brAddrCalc_pc[37:35] < repBound__h1625 ;
  assign brAddrCalc_val_BITS_159_TO_110_7_XOR_SEXT_brAd_ETC___d94 =
	     (highOffsetBits__h618 == 50'd0 &&
	      IF_brAddrCalc_val_BIT_159_8_THEN_NOT_brAddrCal_ETC___d91 ||
	      NOT_brAddrCalc_pc_BITS_43_TO_38_ULT_50_6___d27) &&
	     brAddrCalc_pc[162] ;
  assign cap_capFat_addrBits__h848 =
	     brAddrCalc_cap ?
	       brAddrCalc_val[95:82] :
	       result_d_addrBits__h839 ;
  assign cap_capFat_address__h847 =
	     brAddrCalc_cap ?
	       brAddrCalc_val[161:96] :
	       result_d_address__h838 ;
  assign cap_capFat_bounds_baseBits__h872 =
	     brAddrCalc_cap ? brAddrCalc_val[23:10] : brAddrCalc_pc[23:10] ;
  assign cap_capFat_bounds_topBits__h871 =
	     brAddrCalc_cap ? brAddrCalc_val[37:24] : brAddrCalc_pc[37:24] ;
  assign cap_tempFields_repBoundTopBits__h991 =
	     brAddrCalc_cap ? brAddrCalc_val[9:7] : repBound__h1625 ;
  assign highBitsfilter__h524 =
	     50'h3FFFFFFFFFFFF <<
	     IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_43__ETC___d37 ;
  assign highOffsetBits__h127 = x__h552 & mask__h1109 ;
  assign highOffsetBits__h525 = x__h552 & highBitsfilter__h524 ;
  assign highOffsetBits__h618 = x__h645 & mask__h1109 ;
  assign inc__h105 = (brAddrCalc_orig_inst[1:0] == 2'b11) ? 12'd4 : 12'd2 ;
  assign jumpTarget_capFat_flags__h437 =
	     brAddrCalc_cap ? brAddrCalc_val[65] : brAddrCalc_pc[65] ;
  assign jumpTarget_capFat_reserved__h438 =
	     brAddrCalc_cap ? brAddrCalc_val[64:63] : brAddrCalc_pc[64:63] ;
  assign mask__h1109 = 50'h3FFFFFFFFFFFF << brAddrCalc_pc[43:38] ;
  assign newAddrBits__h827 =
	     { 2'd0, brAddrCalc_pc[23:10] } + { 2'd0, x__h766[13:0] } ;
  assign pointer__h118 = brAddrCalc_pc[161:96] + { 2'd0, brAddrCalc_imm } ;
  assign pointer__h445 = { 2'd0, address__h106 } ;
  assign pointer__h487 = { 2'd0, address__h480 } ;
  assign pointer__h516 = cap_capFat_address__h847 + { 2'd0, brAddrCalc_imm } ;
  assign repBoundBits__h133 = { brAddrCalc_pc[9:7], 11'd0 } ;
  assign repBoundBits__h531 =
	     { cap_tempFields_repBoundTopBits__h991, 11'd0 } ;
  assign repBound__h1615 = cap_capFat_bounds_baseBits__h872[13:11] - 3'b001 ;
  assign repBound__h1625 = brAddrCalc_pc[23:21] - 3'b001 ;
  assign result_d_addrBits__h839 =
	     (brAddrCalc_pc[43:38] == 6'd52) ?
	       { 1'b0, newAddrBits__h827[12:0] } :
	       newAddrBits__h827[13:0] ;
  assign result_d_address__h838 =
	     { 2'd0, bot__h1111 } + { 2'd0, brAddrCalc_val[159:96] } ;
  assign signBits__h522 = {50{brAddrCalc_imm[63]}} ;
  assign signBits__h615 = {50{brAddrCalc_val[159]}} ;
  assign targetAddr_capFat_address__h460 =
	     { 2'd0,
	       IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_pc_BI_ETC___d131 } ;
  assign toBoundsM1__h137 = repBoundBits__h133 + ~brAddrCalc_pc[95:82] ;
  assign toBoundsM1__h535 = repBoundBits__h531 + ~cap_capFat_addrBits__h848 ;
  assign toBoundsM1__h628 = { 3'b110, ~brAddrCalc_pc[20:10] } ;
  assign toBounds__h136 = repBoundBits__h133 - brAddrCalc_pc[95:82] ;
  assign toBounds__h534 = repBoundBits__h531 - cap_capFat_addrBits__h848 ;
  assign toBounds__h627 = 14'd14336 - { 3'b0, brAddrCalc_pc[20:10] } ;
  assign x__h1165 = { brAddrCalc_pc[1:0], brAddrCalc_pc[23:10] } ;
  assign x__h1250 = pointer__h118 >> brAddrCalc_pc[43:38] ;
  assign x__h1280 =
	     pointer__h487 >>
	     IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_43__ETC___d37 ;
  assign x__h1311 = pointer__h445 >> brAddrCalc_pc[43:38] ;
  assign x__h309 = brAddrCalc_imm >> brAddrCalc_pc[43:38] ;
  assign x__h552 = brAddrCalc_imm[63:14] ^ signBits__h522 ;
  assign x__h645 = brAddrCalc_val[159:110] ^ signBits__h615 ;
  assign x__h766 = brAddrCalc_val[159:96] >> brAddrCalc_pc[43:38] ;
  assign x__h940 =
	     brAddrCalc_imm >>
	     IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_43__ETC___d37 ;
  always@(brAddrCalc_iType or
	  address__h106 or pointer__h118 or address__h480 or brAddrCalc_taken)
  begin
    case (brAddrCalc_iType)
      5'd8:
	  IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_pc_BI_ETC___d131 =
	      pointer__h118[63:0];
      5'd9, 5'd11, 5'd12:
	  IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_pc_BI_ETC___d131 =
	      address__h480;
      5'd10:
	  IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_pc_BI_ETC___d131 =
	      brAddrCalc_taken ? pointer__h118[63:0] : address__h106;
      default: IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_pc_BI_ETC___d131 =
		   address__h106;
    endcase
  end
  always@(brAddrCalc_iType or
	  IF_brAddrCalc_iType_EQ_10_7_THEN_IF_brAddrCalc_ETC___d159 or
	  brAddrCalc_pc or
	  x__h1250 or
	  _0_CONCAT_IF_brAddrCalc_cap_THEN_brAddrCalc_val_ETC___d154)
  begin
    case (brAddrCalc_iType)
      5'd8:
	  IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_pc_BI_ETC___d162 =
	      { x__h1250[13:0], brAddrCalc_pc[81:10] };
      5'd9, 5'd11, 5'd12:
	  IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_pc_BI_ETC___d162 =
	      _0_CONCAT_IF_brAddrCalc_cap_THEN_brAddrCalc_val_ETC___d154;
      default: IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_pc_BI_ETC___d162 =
		   { IF_brAddrCalc_iType_EQ_10_7_THEN_IF_brAddrCalc_ETC___d159,
		     brAddrCalc_pc[81:10] };
    endcase
  end
  always@(brAddrCalc_iType or
	  brAddrCalc_pc or
	  brAddrCalc_imm_BITS_63_TO_14_XOR_SEXT_brAddrCa_ETC___d30 or
	  brAddrCalc_imm_BITS_63_TO_14_XOR_SEXT_brAddrCa_ETC___d96 or
	  brAddrCalc_taken)
  begin
    case (brAddrCalc_iType)
      5'd8:
	  IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_imm_B_ETC___d101 =
	      brAddrCalc_imm_BITS_63_TO_14_XOR_SEXT_brAddrCa_ETC___d30;
      5'd9, 5'd11, 5'd12:
	  IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_imm_B_ETC___d101 =
	      brAddrCalc_imm_BITS_63_TO_14_XOR_SEXT_brAddrCa_ETC___d96;
      5'd10:
	  IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_imm_B_ETC___d101 =
	      brAddrCalc_taken ?
		brAddrCalc_imm_BITS_63_TO_14_XOR_SEXT_brAddrCa_ETC___d30 :
		brAddrCalc_pc[162];
      default: IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_imm_B_ETC___d101 =
		   brAddrCalc_pc[162];
    endcase
  end
  always@(brAddrCalc_iType or
	  repBound__h1625 or
	  brAddrCalc_pc_BITS_37_TO_35_64_ULT_brAddrCalc__ETC___d165 or
	  brAddrCalc_pc_BITS_23_TO_21_4_ULT_brAddrCalc_p_ETC___d166 or
	  IF_brAddrCalc_iType_EQ_10_7_THEN_IF_brAddrCalc_ETC___d218 or
	  brAddrCalc_pc_BITS_161_TO_96_02_PLUS_0_CONCAT__ETC___d178 or
	  repBound__h1615 or
	  IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_37__ETC___d189 or
	  IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_23__ETC___d190 or
	  _0_CONCAT_IF_brAddrCalc_cap_THEN_brAddrCalc_val_ETC___d192 or
	  IF_IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS__ETC___d202)
  begin
    case (brAddrCalc_iType)
      5'd8:
	  IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_pc_BI_ETC___d222 =
	      { repBound__h1625,
		brAddrCalc_pc_BITS_37_TO_35_64_ULT_brAddrCalc__ETC___d165,
		brAddrCalc_pc_BITS_23_TO_21_4_ULT_brAddrCalc_p_ETC___d166,
		brAddrCalc_pc_BITS_161_TO_96_02_PLUS_0_CONCAT__ETC___d178 };
      5'd9, 5'd11, 5'd12:
	  IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_pc_BI_ETC___d222 =
	      { repBound__h1615,
		IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_37__ETC___d189,
		IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS_23__ETC___d190,
		_0_CONCAT_IF_brAddrCalc_cap_THEN_brAddrCalc_val_ETC___d192,
		IF_IF_brAddrCalc_cap_THEN_brAddrCalc_val_BITS__ETC___d202 };
      default: IF_brAddrCalc_iType_EQ_8_THEN_brAddrCalc_pc_BI_ETC___d222 =
		   { repBound__h1625,
		     brAddrCalc_pc_BITS_37_TO_35_64_ULT_brAddrCalc__ETC___d165,
		     brAddrCalc_pc_BITS_23_TO_21_4_ULT_brAddrCalc_p_ETC___d166,
		     IF_brAddrCalc_iType_EQ_10_7_THEN_IF_brAddrCalc_ETC___d218 };
    endcase
  end
endmodule  // module_brAddrCalc


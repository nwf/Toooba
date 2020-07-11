//
// Generated by Bluespec Compiler, version 2019.05.beta2 (build a88bf40db, 2019-05-24)
//
// On Fri Jul 10 21:09:42 BST 2020
//
//
// Ports:
// Name                         I/O  size props
// decodeBrPred                   O   130
// decodeBrPred_pc                I   129
// decodeBrPred_dInst             I   145
// decodeBrPred_histTaken         I     1
// decodeBrPred_is_32b_inst       I     1
//
// Combinational paths from inputs to outputs:
//   (decodeBrPred_pc,
//    decodeBrPred_dInst,
//    decodeBrPred_histTaken,
//    decodeBrPred_is_32b_inst) -> decodeBrPred
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

module module_decodeBrPred(decodeBrPred_pc,
			   decodeBrPred_dInst,
			   decodeBrPred_histTaken,
			   decodeBrPred_is_32b_inst,
			   decodeBrPred);
  // value method decodeBrPred
  input  [128 : 0] decodeBrPred_pc;
  input  [144 : 0] decodeBrPred_dInst;
  input  decodeBrPred_histTaken;
  input  decodeBrPred_is_32b_inst;
  output [129 : 0] decodeBrPred;

  // signals for module outputs
  wire [129 : 0] decodeBrPred;

  // remaining internal signals
  reg [128 : 0] CASE_decodeBrPred_dInst_BITS_144_TO_140_8_jTar_ETC__q4;
  wire [128 : 0] jTarget__h28, pcPlusN__h24;
  wire [65 : 0] cr_address__h336, pointer__h157;
  wire [63 : 0] IF_decodeBrPred_dInst_BIT_32_0_THEN_SEXT_decod_ETC___d23,
		address__h1139,
		x__h635,
		x__h702;
  wire [49 : 0] highBitsfilter__h165,
		highOffsetBits__h166,
		signBits__h163,
		x__h193;
  wire [31 : 0] decodeBrPred_dInst_BITS_31_TO_0__q2;
  wire [25 : 0] IF_INV_decodeBrPred_pc_BITS_108_TO_90_8_9_BIT__ETC___d86;
  wire [18 : 0] INV_decodeBrPred_pc_BITS_108_TO_90__q1;
  wire [13 : 0] b_base__h680,
		cr_addrBits__h337,
		repBoundBits__h172,
		toBoundsM1__h176,
		toBounds__h175,
		x__h673;
  wire [11 : 0] IF_INV_decodeBrPred_pc_BITS_108_TO_90_BIT_0_TH_ETC__q3,
		b_top__h679,
		inc__h1103;
  wire [5 : 0] IF_INV_decodeBrPred_pc_BITS_108_TO_90_8_9_BIT__ETC___d40;
  wire [2 : 0] b_expBotHalf__h571, b_expTopHalf__h569, repBound__h666;
  wire IF_IF_decodeBrPred_dInst_BIT_32_0_THEN_SEXT_de_ETC___d67,
       IF_decodeBrPred_dInst_BIT_32_0_THEN_SEXT_decod_ETC___d73;

  // value method decodeBrPred
  assign decodeBrPred =
	     { decodeBrPred_dInst[144:140] != 5'd9 &&
	       decodeBrPred_dInst[144:140] != 5'd11 &&
	       decodeBrPred_dInst[144:140] != 5'd12,
	       CASE_decodeBrPred_dInst_BITS_144_TO_140_8_jTar_ETC__q4 } ;

  // remaining internal signals
  assign IF_IF_decodeBrPred_dInst_BIT_32_0_THEN_SEXT_de_ETC___d67 =
	     IF_decodeBrPred_dInst_BIT_32_0_THEN_SEXT_decod_ETC___d23[63] ?
	       x__h635[13:0] >= toBounds__h175 &&
	       repBoundBits__h172 != cr_addrBits__h337 :
	       x__h635[13:0] < toBoundsM1__h176 ;
  assign IF_INV_decodeBrPred_pc_BITS_108_TO_90_8_9_BIT__ETC___d40 =
	     INV_decodeBrPred_pc_BITS_108_TO_90__q1[0] ?
	       { b_expTopHalf__h569, b_expBotHalf__h571 } :
	       6'd0 ;
  assign IF_INV_decodeBrPred_pc_BITS_108_TO_90_8_9_BIT__ETC___d86 =
	     INV_decodeBrPred_pc_BITS_108_TO_90__q1[0] ?
	       { IF_INV_decodeBrPred_pc_BITS_108_TO_90_BIT_0_TH_ETC__q3[11:3],
		 IF_INV_decodeBrPred_pc_BITS_108_TO_90_8_9_BIT__ETC___d40[5:3],
		 x__h673[13:3],
		 IF_INV_decodeBrPred_pc_BITS_108_TO_90_8_9_BIT__ETC___d40[2:0] } :
	       { b_top__h679, b_base__h680 } ;
  assign IF_INV_decodeBrPred_pc_BITS_108_TO_90_BIT_0_TH_ETC__q3 =
	     INV_decodeBrPred_pc_BITS_108_TO_90__q1[0] ?
	       { decodeBrPred_pc[89:81], 3'd0 } :
	       b_top__h679 ;
  assign IF_decodeBrPred_dInst_BIT_32_0_THEN_SEXT_decod_ETC___d23 =
	     { {32{decodeBrPred_dInst_BITS_31_TO_0__q2[31]}},
	       decodeBrPred_dInst_BITS_31_TO_0__q2 } ;
  assign IF_decodeBrPred_dInst_BIT_32_0_THEN_SEXT_decod_ETC___d73 =
	     (highOffsetBits__h166 == 50'd0 &&
	      IF_IF_decodeBrPred_dInst_BIT_32_0_THEN_SEXT_de_ETC___d67 ||
	      IF_INV_decodeBrPred_pc_BITS_108_TO_90_8_9_BIT__ETC___d40 >=
	      6'd50) &&
	     decodeBrPred_pc[128] ;
  assign INV_decodeBrPred_pc_BITS_108_TO_90__q1 = ~decodeBrPred_pc[108:90] ;
  assign address__h1139 =
	     decodeBrPred_pc[63:0] + { {52{inc__h1103[11]}}, inc__h1103 } ;
  assign b_base__h680 =
	     { decodeBrPred_pc[77:67],
	       ~decodeBrPred_pc[66],
	       decodeBrPred_pc[65:64] } ;
  assign b_expBotHalf__h571 =
	     { ~decodeBrPred_pc[66], decodeBrPred_pc[65:64] } ;
  assign b_expTopHalf__h569 =
	     { ~decodeBrPred_pc[80:79], decodeBrPred_pc[78] } ;
  assign b_top__h679 =
	     { decodeBrPred_pc[89:81],
	       ~decodeBrPred_pc[80:79],
	       decodeBrPred_pc[78] } ;
  assign cr_addrBits__h337 =
	     INV_decodeBrPred_pc_BITS_108_TO_90__q1[0] ?
	       x__h702[13:0] :
	       decodeBrPred_pc[13:0] ;
  assign cr_address__h336 = { 2'd0, decodeBrPred_pc[63:0] } ;
  assign decodeBrPred_dInst_BITS_31_TO_0__q2 = decodeBrPred_dInst[31:0] ;
  assign highBitsfilter__h165 =
	     50'h3FFFFFFFFFFFF <<
	     IF_INV_decodeBrPred_pc_BITS_108_TO_90_8_9_BIT__ETC___d40 ;
  assign highOffsetBits__h166 = x__h193 & highBitsfilter__h165 ;
  assign inc__h1103 = decodeBrPred_is_32b_inst ? 12'd4 : 12'd2 ;
  assign jTarget__h28 =
	     { IF_decodeBrPred_dInst_BIT_32_0_THEN_SEXT_decod_ETC___d73,
	       decodeBrPred_pc[127:90],
	       IF_INV_decodeBrPred_pc_BITS_108_TO_90_8_9_BIT__ETC___d86[25:17],
	       ~IF_INV_decodeBrPred_pc_BITS_108_TO_90_8_9_BIT__ETC___d86[16:15],
	       IF_INV_decodeBrPred_pc_BITS_108_TO_90_8_9_BIT__ETC___d86[14:3],
	       ~IF_INV_decodeBrPred_pc_BITS_108_TO_90_8_9_BIT__ETC___d86[2],
	       IF_INV_decodeBrPred_pc_BITS_108_TO_90_8_9_BIT__ETC___d86[1:0],
	       pointer__h157[63:0] } ;
  assign pcPlusN__h24 = { decodeBrPred_pc[128:64], address__h1139 } ;
  assign pointer__h157 =
	     cr_address__h336 +
	     { 2'd0,
	       IF_decodeBrPred_dInst_BIT_32_0_THEN_SEXT_decod_ETC___d23 } ;
  assign repBoundBits__h172 = { repBound__h666, 11'd0 } ;
  assign repBound__h666 = x__h673[13:11] - 3'b001 ;
  assign signBits__h163 =
	     {50{IF_decodeBrPred_dInst_BIT_32_0_THEN_SEXT_decod_ETC___d23[63]}} ;
  assign toBoundsM1__h176 = repBoundBits__h172 + ~cr_addrBits__h337 ;
  assign toBounds__h175 = repBoundBits__h172 - cr_addrBits__h337 ;
  assign x__h193 =
	     IF_decodeBrPred_dInst_BIT_32_0_THEN_SEXT_decod_ETC___d23[63:14] ^
	     signBits__h163 ;
  assign x__h635 =
	     IF_decodeBrPred_dInst_BIT_32_0_THEN_SEXT_decod_ETC___d23 >>
	     IF_INV_decodeBrPred_pc_BITS_108_TO_90_8_9_BIT__ETC___d40 ;
  assign x__h673 =
	     INV_decodeBrPred_pc_BITS_108_TO_90__q1[0] ?
	       { decodeBrPred_pc[77:67], 3'd0 } :
	       b_base__h680 ;
  assign x__h702 =
	     decodeBrPred_pc[63:0] >>
	     { b_expTopHalf__h569, b_expBotHalf__h571 } ;
  always@(decodeBrPred_dInst or
	  pcPlusN__h24 or jTarget__h28 or decodeBrPred_histTaken)
  begin
    case (decodeBrPred_dInst[144:140])
      5'd8:
	  CASE_decodeBrPred_dInst_BITS_144_TO_140_8_jTar_ETC__q4 =
	      jTarget__h28;
      5'd10:
	  CASE_decodeBrPred_dInst_BITS_144_TO_140_8_jTar_ETC__q4 =
	      decodeBrPred_histTaken ? jTarget__h28 : pcPlusN__h24;
      default: CASE_decodeBrPred_dInst_BITS_144_TO_140_8_jTar_ETC__q4 =
		   pcPlusN__h24;
    endcase
  end
endmodule  // module_decodeBrPred


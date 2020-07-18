//
// Generated by Bluespec Compiler, version 2019.05.beta2 (build a88bf40db, 2019-05-24)
//
// On Sat Jul 18 16:00:05 BST 2020
//
//
// Ports:
// Name                         I/O  size props
// amoExec                        O   129
// amoExec_amo_inst               I     8
// amoExec_wordIdx                I     2
// amoExec_current                I   129
// amoExec_inpt                   I   129
//
// Combinational paths from inputs to outputs:
//   (amoExec_amo_inst,
//    amoExec_wordIdx,
//    amoExec_current,
//    amoExec_inpt) -> amoExec
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

module module_amoExec(amoExec_amo_inst,
		      amoExec_wordIdx,
		      amoExec_current,
		      amoExec_inpt,
		      amoExec);
  // value method amoExec
  input  [7 : 0] amoExec_amo_inst;
  input  [1 : 0] amoExec_wordIdx;
  input  [128 : 0] amoExec_current;
  input  [128 : 0] amoExec_inpt;
  output [128 : 0] amoExec;

  // signals for module outputs
  wire [128 : 0] amoExec;

  // remaining internal signals
  reg [127 : 0] tmpData__h32, x__h611, x__h700;
  reg [63 : 0] vOld__h709, x__h707;
  reg [31 : 0] vOld__h1136, x__h1134;
  reg [7 : 0] shftAmnt__h37;
  wire [127 : 0] tmpData__h632,
		 tmpData__h638,
		 x__h325,
		 x__h610,
		 y__h326,
		 y__h328;
  wire [7 : 0] shftAmnt__h634, shftAmnt__h640;
  wire SEL_ARR_amoExec_current_BITS_31_TO_0_3_amoExec_ETC___d63,
       SEL_ARR_amoExec_current_BITS_31_TO_0_3_amoExec_ETC___d66,
       SEL_ARR_amoExec_current_BITS_63_TO_0_3_amoExec_ETC___d35,
       SEL_ARR_amoExec_current_BITS_63_TO_0_3_amoExec_ETC___d40,
       amoExec_current_BITS_127_TO_0_SLE_amoExec_inpt_ETC___d90,
       amoExec_current_BITS_127_TO_0_ULE_amoExec_inpt_ETC___d93;

  // value method amoExec
  assign amoExec =
	     { amoExec_amo_inst[7:4] == 4'd0 &&
	       amoExec_amo_inst[3:2] == 2'd0 &&
	       amoExec_inpt[128],
	       x__h325 | y__h326 } ;

  // remaining internal signals
  assign SEL_ARR_amoExec_current_BITS_31_TO_0_3_amoExec_ETC___d63 =
	     (vOld__h1136 ^ 32'h80000000) <=
	     (amoExec_inpt[31:0] ^ 32'h80000000) ;
  assign SEL_ARR_amoExec_current_BITS_31_TO_0_3_amoExec_ETC___d66 =
	     vOld__h1136 <= amoExec_inpt[31:0] ;
  assign SEL_ARR_amoExec_current_BITS_63_TO_0_3_amoExec_ETC___d35 =
	     (vOld__h709 ^ 64'h8000000000000000) <=
	     (amoExec_inpt[63:0] ^ 64'h8000000000000000) ;
  assign SEL_ARR_amoExec_current_BITS_63_TO_0_3_amoExec_ETC___d40 =
	     vOld__h709 <= amoExec_inpt[63:0] ;
  assign amoExec_current_BITS_127_TO_0_SLE_amoExec_inpt_ETC___d90 =
	     (amoExec_current[127:0] ^
	      128'h80000000000000000000000000000000) <=
	     (amoExec_inpt[127:0] ^ 128'h80000000000000000000000000000000) ;
  assign amoExec_current_BITS_127_TO_0_ULE_amoExec_inpt_ETC___d93 =
	     amoExec_current[127:0] <= amoExec_inpt[127:0] ;
  assign shftAmnt__h634 = { 1'd0, amoExec_wordIdx[1], 6'd0 } ;
  assign shftAmnt__h640 = { 1'd0, amoExec_wordIdx, 5'd0 } ;
  assign tmpData__h632 = { 64'd0, x__h707 } ;
  assign tmpData__h638 = { 96'd0, x__h1134 } ;
  assign x__h325 = amoExec_current[127:0] & y__h328 ;
  assign x__h610 = x__h611 << shftAmnt__h37 ;
  assign y__h326 = x__h700 << shftAmnt__h37 ;
  assign y__h328 = ~x__h610 ;
  always@(amoExec_wordIdx or amoExec_current)
  begin
    case (amoExec_wordIdx[1])
      1'd0: vOld__h709 = amoExec_current[63:0];
      1'd1: vOld__h709 = amoExec_current[127:64];
    endcase
  end
  always@(amoExec_wordIdx or amoExec_current)
  begin
    case (amoExec_wordIdx)
      2'd0: vOld__h1136 = amoExec_current[31:0];
      2'd1: vOld__h1136 = amoExec_current[63:32];
      2'd2: vOld__h1136 = amoExec_current[95:64];
      2'd3: vOld__h1136 = amoExec_current[127:96];
    endcase
  end
  always@(amoExec_amo_inst)
  begin
    case (amoExec_amo_inst[3:2])
      2'd1: x__h611 = 128'h0000000000000000FFFFFFFFFFFFFFFF;
      2'd2: x__h611 = 128'h000000000000000000000000FFFFFFFF;
      default: x__h611 = 128'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
    endcase
  end
  always@(amoExec_amo_inst or shftAmnt__h634 or shftAmnt__h640)
  begin
    case (amoExec_amo_inst[3:2])
      2'd1: shftAmnt__h37 = shftAmnt__h634;
      2'd2: shftAmnt__h37 = shftAmnt__h640;
      default: shftAmnt__h37 = 8'd0;
    endcase
  end
  always@(amoExec_amo_inst or
	  SEL_ARR_amoExec_current_BITS_63_TO_0_3_amoExec_ETC___d40 or
	  amoExec_inpt or
	  vOld__h709 or
	  SEL_ARR_amoExec_current_BITS_63_TO_0_3_amoExec_ETC___d35)
  begin
    case (amoExec_amo_inst[7:4])
      4'd0: x__h707 = amoExec_inpt[63:0];
      4'd1: x__h707 = vOld__h709 + amoExec_inpt[63:0];
      4'd2: x__h707 = vOld__h709 ^ amoExec_inpt[63:0];
      4'd3: x__h707 = vOld__h709 & amoExec_inpt[63:0];
      4'd4: x__h707 = vOld__h709 | amoExec_inpt[63:0];
      4'd5:
	  x__h707 =
	      SEL_ARR_amoExec_current_BITS_63_TO_0_3_amoExec_ETC___d35 ?
		vOld__h709 :
		amoExec_inpt[63:0];
      4'd6:
	  x__h707 =
	      SEL_ARR_amoExec_current_BITS_63_TO_0_3_amoExec_ETC___d35 ?
		amoExec_inpt[63:0] :
		vOld__h709;
      4'd7:
	  x__h707 =
	      SEL_ARR_amoExec_current_BITS_63_TO_0_3_amoExec_ETC___d40 ?
		vOld__h709 :
		amoExec_inpt[63:0];
      default: x__h707 =
		   SEL_ARR_amoExec_current_BITS_63_TO_0_3_amoExec_ETC___d40 ?
		     amoExec_inpt[63:0] :
		     vOld__h709;
    endcase
  end
  always@(amoExec_amo_inst or
	  SEL_ARR_amoExec_current_BITS_31_TO_0_3_amoExec_ETC___d66 or
	  amoExec_inpt or
	  vOld__h1136 or
	  SEL_ARR_amoExec_current_BITS_31_TO_0_3_amoExec_ETC___d63)
  begin
    case (amoExec_amo_inst[7:4])
      4'd0: x__h1134 = amoExec_inpt[31:0];
      4'd1: x__h1134 = vOld__h1136 + amoExec_inpt[31:0];
      4'd2: x__h1134 = vOld__h1136 ^ amoExec_inpt[31:0];
      4'd3: x__h1134 = vOld__h1136 & amoExec_inpt[31:0];
      4'd4: x__h1134 = vOld__h1136 | amoExec_inpt[31:0];
      4'd5:
	  x__h1134 =
	      SEL_ARR_amoExec_current_BITS_31_TO_0_3_amoExec_ETC___d63 ?
		vOld__h1136 :
		amoExec_inpt[31:0];
      4'd6:
	  x__h1134 =
	      SEL_ARR_amoExec_current_BITS_31_TO_0_3_amoExec_ETC___d63 ?
		amoExec_inpt[31:0] :
		vOld__h1136;
      4'd7:
	  x__h1134 =
	      SEL_ARR_amoExec_current_BITS_31_TO_0_3_amoExec_ETC___d66 ?
		vOld__h1136 :
		amoExec_inpt[31:0];
      default: x__h1134 =
		   SEL_ARR_amoExec_current_BITS_31_TO_0_3_amoExec_ETC___d66 ?
		     amoExec_inpt[31:0] :
		     vOld__h1136;
    endcase
  end
  always@(amoExec_amo_inst or
	  amoExec_current_BITS_127_TO_0_ULE_amoExec_inpt_ETC___d93 or
	  amoExec_inpt or
	  amoExec_current or
	  amoExec_current_BITS_127_TO_0_SLE_amoExec_inpt_ETC___d90)
  begin
    case (amoExec_amo_inst[7:4])
      4'd0: tmpData__h32 = amoExec_inpt[127:0];
      4'd1: tmpData__h32 = amoExec_current[127:0] + amoExec_inpt[127:0];
      4'd2:
	  tmpData__h32 =
	      { amoExec_current[127:64] ^ amoExec_inpt[127:64],
		amoExec_current[63:0] ^ amoExec_inpt[63:0] };
      4'd3:
	  tmpData__h32 =
	      { amoExec_current[127:64] & amoExec_inpt[127:64],
		amoExec_current[63:0] & amoExec_inpt[63:0] };
      4'd4:
	  tmpData__h32 =
	      { amoExec_current[127:64] | amoExec_inpt[127:64],
		amoExec_current[63:0] | amoExec_inpt[63:0] };
      4'd5:
	  tmpData__h32 =
	      amoExec_current_BITS_127_TO_0_SLE_amoExec_inpt_ETC___d90 ?
		amoExec_current[127:0] :
		amoExec_inpt[127:0];
      4'd6:
	  tmpData__h32 =
	      amoExec_current_BITS_127_TO_0_SLE_amoExec_inpt_ETC___d90 ?
		amoExec_inpt[127:0] :
		amoExec_current[127:0];
      4'd7:
	  tmpData__h32 =
	      amoExec_current_BITS_127_TO_0_ULE_amoExec_inpt_ETC___d93 ?
		amoExec_current[127:0] :
		amoExec_inpt[127:0];
      default: tmpData__h32 =
		   amoExec_current_BITS_127_TO_0_ULE_amoExec_inpt_ETC___d93 ?
		     amoExec_inpt[127:0] :
		     amoExec_current[127:0];
    endcase
  end
  always@(amoExec_amo_inst or tmpData__h32 or tmpData__h632 or tmpData__h638)
  begin
    case (amoExec_amo_inst[3:2])
      2'd1: x__h700 = tmpData__h632;
      2'd2: x__h700 = tmpData__h638;
      default: x__h700 = tmpData__h32;
    endcase
  end
endmodule  // module_amoExec


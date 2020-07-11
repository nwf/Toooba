//
// Generated by Bluespec Compiler, version 2019.05.beta2 (build a88bf40db, 2019-05-24)
//
// On Fri Jul 10 20:51:38 BST 2020
//
//
// Ports:
// Name                         I/O  size props
// aluBr                          O     1
// aluBr_a                        I    64
// aluBr_b                        I    64
// aluBr_brFunc                   I     3
//
// Combinational paths from inputs to outputs:
//   (aluBr_a, aluBr_b, aluBr_brFunc) -> aluBr
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

module module_aluBr(aluBr_a,
		    aluBr_b,
		    aluBr_brFunc,
		    aluBr);
  // value method aluBr
  input  [63 : 0] aluBr_a;
  input  [63 : 0] aluBr_b;
  input  [2 : 0] aluBr_brFunc;
  output aluBr;

  // signals for module outputs
  reg aluBr;

  // remaining internal signals
  wire aluBr_a_EQ_aluBr_b___d2,
       aluBr_a_SLT_aluBr_b___d6,
       aluBr_a_ULT_aluBr_b___d8;

  // value method aluBr
  always@(aluBr_brFunc or
	  aluBr_a_EQ_aluBr_b___d2 or
	  aluBr_a_SLT_aluBr_b___d6 or aluBr_a_ULT_aluBr_b___d8)
  begin
    case (aluBr_brFunc)
      3'd0: aluBr = aluBr_a_EQ_aluBr_b___d2;
      3'd1: aluBr = !aluBr_a_EQ_aluBr_b___d2;
      3'd2: aluBr = aluBr_a_SLT_aluBr_b___d6;
      3'd3: aluBr = aluBr_a_ULT_aluBr_b___d8;
      3'd4: aluBr = !aluBr_a_SLT_aluBr_b___d6;
      3'd5: aluBr = !aluBr_a_ULT_aluBr_b___d8;
      default: aluBr = aluBr_brFunc == 3'd6;
    endcase
  end

  // remaining internal signals
  assign aluBr_a_EQ_aluBr_b___d2 = aluBr_a == aluBr_b ;
  assign aluBr_a_SLT_aluBr_b___d6 =
	     (aluBr_a ^ 64'h8000000000000000) <
	     (aluBr_b ^ 64'h8000000000000000) ;
  assign aluBr_a_ULT_aluBr_b___d8 = aluBr_a < aluBr_b ;
endmodule  // module_aluBr


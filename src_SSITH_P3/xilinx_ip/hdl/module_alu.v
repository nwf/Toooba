//
// Generated by Bluespec Compiler, version 2019.05.beta2 (build a88bf40db, 2019-05-24)
//
// On Mon Jul 13 18:40:11 BST 2020
//
//
// Ports:
// Name                         I/O  size props
// alu                            O    64
// alu_a                          I    64
// alu_b                          I    64
// alu_func                       I     5
//
// Combinational paths from inputs to outputs:
//   (alu_a, alu_b, alu_func) -> alu
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

module module_alu(alu_a,
		  alu_b,
		  alu_func,
		  alu);
  // value method alu
  input  [63 : 0] alu_a;
  input  [63 : 0] alu_b;
  input  [4 : 0] alu_func;
  output [63 : 0] alu;

  // signals for module outputs
  reg [63 : 0] alu;

  // remaining internal signals
  wire [63 : 0] alu_a_OR_alu_b___d16, alu_a_PLUS_alu_b___d2, y__h569;
  wire [31 : 0] alu_a_BITS_31_TO_0__q1,
		alu_a_PLUS_alu_b_BITS_31_TO_0__q2,
		x__h109,
		x__h266,
		x__h420,
		x__h490;
  wire x__h205, x__h213;

  // value method alu
  always@(alu_func or
	  alu_a_PLUS_alu_b___d2 or
	  alu_a_PLUS_alu_b_BITS_31_TO_0__q2 or
	  alu_a or
	  alu_b or
	  x__h109 or
	  alu_a_OR_alu_b___d16 or
	  x__h205 or x__h213 or x__h266 or x__h490 or x__h420 or y__h569)
  begin
    case (alu_func)
      5'd0: alu = alu_a_PLUS_alu_b___d2;
      5'd1:
	  alu =
	      { {32{alu_a_PLUS_alu_b_BITS_31_TO_0__q2[31]}},
		alu_a_PLUS_alu_b_BITS_31_TO_0__q2 };
      5'd2: alu = alu_a - alu_b;
      5'd3: alu = { {32{x__h109[31]}}, x__h109 };
      5'd4: alu = alu_a & alu_b;
      5'd5, 5'd16: alu = alu_a_OR_alu_b___d16;
      5'd6: alu = alu_a ^ alu_b;
      5'd7: alu = { 63'd0, x__h205 };
      5'd8: alu = { 63'd0, x__h213 };
      5'd9: alu = alu_a << alu_b[5:0];
      5'd10: alu = { {32{x__h266[31]}}, x__h266 };
      5'd11:
	  alu =
	      alu_a >> alu_b[5:0] |
	      ~(64'hFFFFFFFFFFFFFFFF >> alu_b[5:0]) & {64{alu_a[63]}};
      5'd12: alu = { {32{x__h490[31]}}, x__h490 };
      5'd13: alu = alu_a >> alu_b[5:0];
      5'd14: alu = { {32{x__h420[31]}}, x__h420 };
      5'd15: alu = alu_b;
      5'd17: alu = alu_a & y__h569;
      default: alu = 64'd0;
    endcase
  end

  // remaining internal signals
  assign alu_a_BITS_31_TO_0__q1 = alu_a[31:0] ;
  assign alu_a_OR_alu_b___d16 = alu_a | alu_b ;
  assign alu_a_PLUS_alu_b_BITS_31_TO_0__q2 = alu_a_PLUS_alu_b___d2[31:0] ;
  assign alu_a_PLUS_alu_b___d2 = alu_a + alu_b ;
  assign x__h109 = alu_a[31:0] - alu_b[31:0] ;
  assign x__h205 =
	     (alu_a ^ 64'h8000000000000000) < (alu_b ^ 64'h8000000000000000) ;
  assign x__h213 = alu_a < alu_b ;
  assign x__h266 = alu_a[31:0] << alu_b[4:0] ;
  assign x__h420 = alu_a[31:0] >> alu_b[4:0] ;
  assign x__h490 =
	     alu_a[31:0] >> alu_b[4:0] |
	     ~(32'hFFFFFFFF >> alu_b[4:0]) &
	     {32{alu_a_BITS_31_TO_0__q1[31]}} ;
  assign y__h569 = ~alu_b ;
endmodule  // module_alu


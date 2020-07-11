//
// Generated by Bluespec Compiler, version 2019.05.beta2 (build a88bf40db, 2019-05-24)
//
// On Fri Jul 10 20:56:14 BST 2020
//
//
// Ports:
// Name                         I/O  size props
// ras_0_first                    O   129
// RDY_ras_0_first                O     1 const
// RDY_ras_0_popPush              O     1 const
// ras_1_first                    O   129
// RDY_ras_1_first                O     1 const
// RDY_ras_1_popPush              O     1 const
// RDY_flush                      O     1 const
// flush_done                     O     1 const
// RDY_flush_done                 O     1 const
// CLK                            I     1 clock
// RST_N                          I     1 reset
// ras_0_popPush_pop              I     1
// ras_0_popPush_pushAddr         I   130
// ras_1_popPush_pop              I     1
// ras_1_popPush_pushAddr         I   130
// EN_ras_0_popPush               I     1
// EN_ras_1_popPush               I     1
// EN_flush                       I     1 unused
//
// Combinational paths from inputs to outputs:
//   (ras_0_popPush_pop, ras_0_popPush_pushAddr, EN_ras_0_popPush) -> ras_1_first
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

module mkRas(CLK,
	     RST_N,

	     ras_0_first,
	     RDY_ras_0_first,

	     ras_0_popPush_pop,
	     ras_0_popPush_pushAddr,
	     EN_ras_0_popPush,
	     RDY_ras_0_popPush,

	     ras_1_first,
	     RDY_ras_1_first,

	     ras_1_popPush_pop,
	     ras_1_popPush_pushAddr,
	     EN_ras_1_popPush,
	     RDY_ras_1_popPush,

	     EN_flush,
	     RDY_flush,

	     flush_done,
	     RDY_flush_done);
  input  CLK;
  input  RST_N;

  // value method ras_0_first
  output [128 : 0] ras_0_first;
  output RDY_ras_0_first;

  // action method ras_0_popPush
  input  ras_0_popPush_pop;
  input  [129 : 0] ras_0_popPush_pushAddr;
  input  EN_ras_0_popPush;
  output RDY_ras_0_popPush;

  // value method ras_1_first
  output [128 : 0] ras_1_first;
  output RDY_ras_1_first;

  // action method ras_1_popPush
  input  ras_1_popPush_pop;
  input  [129 : 0] ras_1_popPush_pushAddr;
  input  EN_ras_1_popPush;
  output RDY_ras_1_popPush;

  // action method flush
  input  EN_flush;
  output RDY_flush;

  // value method flush_done
  output flush_done;
  output RDY_flush_done;

  // signals for module outputs
  reg [128 : 0] ras_0_first, ras_1_first;
  wire RDY_flush,
       RDY_flush_done,
       RDY_ras_0_first,
       RDY_ras_0_popPush,
       RDY_ras_1_first,
       RDY_ras_1_popPush,
       flush_done;

  // inlined wires
  wire stack_0_lat_0$whas,
       stack_0_lat_1$whas,
       stack_1_lat_0$whas,
       stack_1_lat_1$whas,
       stack_2_lat_0$whas,
       stack_2_lat_1$whas,
       stack_3_lat_0$whas,
       stack_3_lat_1$whas,
       stack_4_lat_0$whas,
       stack_4_lat_1$whas,
       stack_5_lat_0$whas,
       stack_5_lat_1$whas,
       stack_6_lat_0$whas,
       stack_6_lat_1$whas,
       stack_7_lat_0$whas,
       stack_7_lat_1$whas;

  // register head_rl
  reg [2 : 0] head_rl;
  wire [2 : 0] head_rl$D_IN;
  wire head_rl$EN;

  // register stack_0_rl
  reg [128 : 0] stack_0_rl;
  wire [128 : 0] stack_0_rl$D_IN;
  wire stack_0_rl$EN;

  // register stack_1_rl
  reg [128 : 0] stack_1_rl;
  wire [128 : 0] stack_1_rl$D_IN;
  wire stack_1_rl$EN;

  // register stack_2_rl
  reg [128 : 0] stack_2_rl;
  wire [128 : 0] stack_2_rl$D_IN;
  wire stack_2_rl$EN;

  // register stack_3_rl
  reg [128 : 0] stack_3_rl;
  wire [128 : 0] stack_3_rl$D_IN;
  wire stack_3_rl$EN;

  // register stack_4_rl
  reg [128 : 0] stack_4_rl;
  wire [128 : 0] stack_4_rl$D_IN;
  wire stack_4_rl$EN;

  // register stack_5_rl
  reg [128 : 0] stack_5_rl;
  wire [128 : 0] stack_5_rl$D_IN;
  wire stack_5_rl$EN;

  // register stack_6_rl
  reg [128 : 0] stack_6_rl;
  wire [128 : 0] stack_6_rl$D_IN;
  wire stack_6_rl$EN;

  // register stack_7_rl
  reg [128 : 0] stack_7_rl;
  wire [128 : 0] stack_7_rl$D_IN;
  wire stack_7_rl$EN;

  // rule scheduling signals
  wire CAN_FIRE_RL_head_canon,
       CAN_FIRE_RL_stack_0_canon,
       CAN_FIRE_RL_stack_1_canon,
       CAN_FIRE_RL_stack_2_canon,
       CAN_FIRE_RL_stack_3_canon,
       CAN_FIRE_RL_stack_4_canon,
       CAN_FIRE_RL_stack_5_canon,
       CAN_FIRE_RL_stack_6_canon,
       CAN_FIRE_RL_stack_7_canon,
       CAN_FIRE_flush,
       CAN_FIRE_ras_0_popPush,
       CAN_FIRE_ras_1_popPush,
       WILL_FIRE_RL_head_canon,
       WILL_FIRE_RL_stack_0_canon,
       WILL_FIRE_RL_stack_1_canon,
       WILL_FIRE_RL_stack_2_canon,
       WILL_FIRE_RL_stack_3_canon,
       WILL_FIRE_RL_stack_4_canon,
       WILL_FIRE_RL_stack_5_canon,
       WILL_FIRE_RL_stack_6_canon,
       WILL_FIRE_RL_stack_7_canon,
       WILL_FIRE_flush,
       WILL_FIRE_ras_0_popPush,
       WILL_FIRE_ras_1_popPush;

  // remaining internal signals
  wire [128 : 0] n__read__h6276,
		 n__read__h6278,
		 n__read__h6280,
		 n__read__h6282,
		 n__read__h6284,
		 n__read__h6286,
		 n__read__h6288,
		 n__read__h6290;
  wire [2 : 0] _theResult____h5853,
	       _theResult____h6601,
	       h___1__h5927,
	       h___1__h6672,
	       upd__h4823,
	       upd__h6245,
	       v__h5897,
	       v__h6645,
	       x__h6201;

  // value method ras_0_first
  always@(head_rl or
	  stack_0_rl or
	  stack_1_rl or
	  stack_2_rl or
	  stack_3_rl or stack_4_rl or stack_5_rl or stack_6_rl or stack_7_rl)
  begin
    case (head_rl)
      3'd0: ras_0_first = stack_0_rl;
      3'd1: ras_0_first = stack_1_rl;
      3'd2: ras_0_first = stack_2_rl;
      3'd3: ras_0_first = stack_3_rl;
      3'd4: ras_0_first = stack_4_rl;
      3'd5: ras_0_first = stack_5_rl;
      3'd6: ras_0_first = stack_6_rl;
      3'd7: ras_0_first = stack_7_rl;
    endcase
  end
  assign RDY_ras_0_first = 1'd1 ;

  // action method ras_0_popPush
  assign RDY_ras_0_popPush = 1'd1 ;
  assign CAN_FIRE_ras_0_popPush = 1'd1 ;
  assign WILL_FIRE_ras_0_popPush = EN_ras_0_popPush ;

  // value method ras_1_first
  always@(x__h6201 or
	  n__read__h6276 or
	  n__read__h6278 or
	  n__read__h6280 or
	  n__read__h6282 or
	  n__read__h6284 or
	  n__read__h6286 or n__read__h6288 or n__read__h6290)
  begin
    case (x__h6201)
      3'd0: ras_1_first = n__read__h6276;
      3'd1: ras_1_first = n__read__h6278;
      3'd2: ras_1_first = n__read__h6280;
      3'd3: ras_1_first = n__read__h6282;
      3'd4: ras_1_first = n__read__h6284;
      3'd5: ras_1_first = n__read__h6286;
      3'd6: ras_1_first = n__read__h6288;
      3'd7: ras_1_first = n__read__h6290;
    endcase
  end
  assign RDY_ras_1_first = 1'd1 ;

  // action method ras_1_popPush
  assign RDY_ras_1_popPush = 1'd1 ;
  assign CAN_FIRE_ras_1_popPush = 1'd1 ;
  assign WILL_FIRE_ras_1_popPush = EN_ras_1_popPush ;

  // action method flush
  assign RDY_flush = 1'd1 ;
  assign CAN_FIRE_flush = 1'd1 ;
  assign WILL_FIRE_flush = EN_flush ;

  // value method flush_done
  assign flush_done = 1'd1 ;
  assign RDY_flush_done = 1'd1 ;

  // rule RL_stack_0_canon
  assign CAN_FIRE_RL_stack_0_canon = 1'd1 ;
  assign WILL_FIRE_RL_stack_0_canon = 1'd1 ;

  // rule RL_stack_1_canon
  assign CAN_FIRE_RL_stack_1_canon = 1'd1 ;
  assign WILL_FIRE_RL_stack_1_canon = 1'd1 ;

  // rule RL_stack_2_canon
  assign CAN_FIRE_RL_stack_2_canon = 1'd1 ;
  assign WILL_FIRE_RL_stack_2_canon = 1'd1 ;

  // rule RL_stack_3_canon
  assign CAN_FIRE_RL_stack_3_canon = 1'd1 ;
  assign WILL_FIRE_RL_stack_3_canon = 1'd1 ;

  // rule RL_stack_4_canon
  assign CAN_FIRE_RL_stack_4_canon = 1'd1 ;
  assign WILL_FIRE_RL_stack_4_canon = 1'd1 ;

  // rule RL_stack_5_canon
  assign CAN_FIRE_RL_stack_5_canon = 1'd1 ;
  assign WILL_FIRE_RL_stack_5_canon = 1'd1 ;

  // rule RL_stack_6_canon
  assign CAN_FIRE_RL_stack_6_canon = 1'd1 ;
  assign WILL_FIRE_RL_stack_6_canon = 1'd1 ;

  // rule RL_stack_7_canon
  assign CAN_FIRE_RL_stack_7_canon = 1'd1 ;
  assign WILL_FIRE_RL_stack_7_canon = 1'd1 ;

  // rule RL_head_canon
  assign CAN_FIRE_RL_head_canon = 1'd1 ;
  assign WILL_FIRE_RL_head_canon = 1'd1 ;

  // inlined wires
  assign stack_0_lat_0$whas =
	     EN_ras_0_popPush && v__h5897 == 3'd0 &&
	     ras_0_popPush_pushAddr[129] ;
  assign stack_0_lat_1$whas =
	     EN_ras_1_popPush && v__h6645 == 3'd0 &&
	     ras_1_popPush_pushAddr[129] ;
  assign stack_1_lat_0$whas =
	     EN_ras_0_popPush && v__h5897 == 3'd1 &&
	     ras_0_popPush_pushAddr[129] ;
  assign stack_1_lat_1$whas =
	     EN_ras_1_popPush && v__h6645 == 3'd1 &&
	     ras_1_popPush_pushAddr[129] ;
  assign stack_2_lat_0$whas =
	     EN_ras_0_popPush && v__h5897 == 3'd2 &&
	     ras_0_popPush_pushAddr[129] ;
  assign stack_2_lat_1$whas =
	     EN_ras_1_popPush && v__h6645 == 3'd2 &&
	     ras_1_popPush_pushAddr[129] ;
  assign stack_3_lat_0$whas =
	     EN_ras_0_popPush && v__h5897 == 3'd3 &&
	     ras_0_popPush_pushAddr[129] ;
  assign stack_3_lat_1$whas =
	     EN_ras_1_popPush && v__h6645 == 3'd3 &&
	     ras_1_popPush_pushAddr[129] ;
  assign stack_4_lat_0$whas =
	     EN_ras_0_popPush && v__h5897 == 3'd4 &&
	     ras_0_popPush_pushAddr[129] ;
  assign stack_4_lat_1$whas =
	     EN_ras_1_popPush && v__h6645 == 3'd4 &&
	     ras_1_popPush_pushAddr[129] ;
  assign stack_5_lat_0$whas =
	     EN_ras_0_popPush && v__h5897 == 3'd5 &&
	     ras_0_popPush_pushAddr[129] ;
  assign stack_5_lat_1$whas =
	     EN_ras_1_popPush && v__h6645 == 3'd5 &&
	     ras_1_popPush_pushAddr[129] ;
  assign stack_6_lat_0$whas =
	     EN_ras_0_popPush && v__h5897 == 3'd6 &&
	     ras_0_popPush_pushAddr[129] ;
  assign stack_6_lat_1$whas =
	     EN_ras_1_popPush && v__h6645 == 3'd6 &&
	     ras_1_popPush_pushAddr[129] ;
  assign stack_7_lat_0$whas =
	     EN_ras_0_popPush && v__h5897 == 3'd7 &&
	     ras_0_popPush_pushAddr[129] ;
  assign stack_7_lat_1$whas =
	     EN_ras_1_popPush && v__h6645 == 3'd7 &&
	     ras_1_popPush_pushAddr[129] ;

  // register head_rl
  assign head_rl$D_IN = EN_ras_1_popPush ? upd__h4823 : x__h6201 ;
  assign head_rl$EN = 1'd1 ;

  // register stack_0_rl
  assign stack_0_rl$D_IN =
	     stack_0_lat_1$whas ?
	       ras_1_popPush_pushAddr[128:0] :
	       n__read__h6276 ;
  assign stack_0_rl$EN = 1'd1 ;

  // register stack_1_rl
  assign stack_1_rl$D_IN =
	     stack_1_lat_1$whas ?
	       ras_1_popPush_pushAddr[128:0] :
	       n__read__h6278 ;
  assign stack_1_rl$EN = 1'd1 ;

  // register stack_2_rl
  assign stack_2_rl$D_IN =
	     stack_2_lat_1$whas ?
	       ras_1_popPush_pushAddr[128:0] :
	       n__read__h6280 ;
  assign stack_2_rl$EN = 1'd1 ;

  // register stack_3_rl
  assign stack_3_rl$D_IN =
	     stack_3_lat_1$whas ?
	       ras_1_popPush_pushAddr[128:0] :
	       n__read__h6282 ;
  assign stack_3_rl$EN = 1'd1 ;

  // register stack_4_rl
  assign stack_4_rl$D_IN =
	     stack_4_lat_1$whas ?
	       ras_1_popPush_pushAddr[128:0] :
	       n__read__h6284 ;
  assign stack_4_rl$EN = 1'd1 ;

  // register stack_5_rl
  assign stack_5_rl$D_IN =
	     stack_5_lat_1$whas ?
	       ras_1_popPush_pushAddr[128:0] :
	       n__read__h6286 ;
  assign stack_5_rl$EN = 1'd1 ;

  // register stack_6_rl
  assign stack_6_rl$D_IN =
	     stack_6_lat_1$whas ?
	       ras_1_popPush_pushAddr[128:0] :
	       n__read__h6288 ;
  assign stack_6_rl$EN = 1'd1 ;

  // register stack_7_rl
  assign stack_7_rl$D_IN =
	     stack_7_lat_1$whas ?
	       ras_1_popPush_pushAddr[128:0] :
	       n__read__h6290 ;
  assign stack_7_rl$EN = 1'd1 ;

  // remaining internal signals
  assign _theResult____h5853 = ras_0_popPush_pop ? h___1__h5927 : head_rl ;
  assign _theResult____h6601 = ras_1_popPush_pop ? h___1__h6672 : x__h6201 ;
  assign h___1__h5927 = head_rl - 3'd1 ;
  assign h___1__h6672 = x__h6201 - 3'd1 ;
  assign n__read__h6276 =
	     stack_0_lat_0$whas ? ras_0_popPush_pushAddr[128:0] : stack_0_rl ;
  assign n__read__h6278 =
	     stack_1_lat_0$whas ? ras_0_popPush_pushAddr[128:0] : stack_1_rl ;
  assign n__read__h6280 =
	     stack_2_lat_0$whas ? ras_0_popPush_pushAddr[128:0] : stack_2_rl ;
  assign n__read__h6282 =
	     stack_3_lat_0$whas ? ras_0_popPush_pushAddr[128:0] : stack_3_rl ;
  assign n__read__h6284 =
	     stack_4_lat_0$whas ? ras_0_popPush_pushAddr[128:0] : stack_4_rl ;
  assign n__read__h6286 =
	     stack_5_lat_0$whas ? ras_0_popPush_pushAddr[128:0] : stack_5_rl ;
  assign n__read__h6288 =
	     stack_6_lat_0$whas ? ras_0_popPush_pushAddr[128:0] : stack_6_rl ;
  assign n__read__h6290 =
	     stack_7_lat_0$whas ? ras_0_popPush_pushAddr[128:0] : stack_7_rl ;
  assign upd__h4823 =
	     ras_1_popPush_pushAddr[129] ? v__h6645 : _theResult____h6601 ;
  assign upd__h6245 =
	     ras_0_popPush_pushAddr[129] ? v__h5897 : _theResult____h5853 ;
  assign v__h5897 = _theResult____h5853 + 3'd1 ;
  assign v__h6645 = _theResult____h6601 + 3'd1 ;
  assign x__h6201 = EN_ras_0_popPush ? upd__h6245 : head_rl ;

  // handling of inlined registers

  always@(posedge CLK)
  begin
    if (RST_N == `BSV_RESET_VALUE)
      begin
        head_rl <= `BSV_ASSIGNMENT_DELAY 3'd0;
	stack_0_rl <= `BSV_ASSIGNMENT_DELAY
	    129'h000001FFFFC0180040000000000000000;
	stack_1_rl <= `BSV_ASSIGNMENT_DELAY
	    129'h000001FFFFC0180040000000000000000;
	stack_2_rl <= `BSV_ASSIGNMENT_DELAY
	    129'h000001FFFFC0180040000000000000000;
	stack_3_rl <= `BSV_ASSIGNMENT_DELAY
	    129'h000001FFFFC0180040000000000000000;
	stack_4_rl <= `BSV_ASSIGNMENT_DELAY
	    129'h000001FFFFC0180040000000000000000;
	stack_5_rl <= `BSV_ASSIGNMENT_DELAY
	    129'h000001FFFFC0180040000000000000000;
	stack_6_rl <= `BSV_ASSIGNMENT_DELAY
	    129'h000001FFFFC0180040000000000000000;
	stack_7_rl <= `BSV_ASSIGNMENT_DELAY
	    129'h000001FFFFC0180040000000000000000;
      end
    else
      begin
        if (head_rl$EN) head_rl <= `BSV_ASSIGNMENT_DELAY head_rl$D_IN;
	if (stack_0_rl$EN)
	  stack_0_rl <= `BSV_ASSIGNMENT_DELAY stack_0_rl$D_IN;
	if (stack_1_rl$EN)
	  stack_1_rl <= `BSV_ASSIGNMENT_DELAY stack_1_rl$D_IN;
	if (stack_2_rl$EN)
	  stack_2_rl <= `BSV_ASSIGNMENT_DELAY stack_2_rl$D_IN;
	if (stack_3_rl$EN)
	  stack_3_rl <= `BSV_ASSIGNMENT_DELAY stack_3_rl$D_IN;
	if (stack_4_rl$EN)
	  stack_4_rl <= `BSV_ASSIGNMENT_DELAY stack_4_rl$D_IN;
	if (stack_5_rl$EN)
	  stack_5_rl <= `BSV_ASSIGNMENT_DELAY stack_5_rl$D_IN;
	if (stack_6_rl$EN)
	  stack_6_rl <= `BSV_ASSIGNMENT_DELAY stack_6_rl$D_IN;
	if (stack_7_rl$EN)
	  stack_7_rl <= `BSV_ASSIGNMENT_DELAY stack_7_rl$D_IN;
      end
  end

  // synopsys translate_off
  `ifdef BSV_NO_INITIAL_BLOCKS
  `else // not BSV_NO_INITIAL_BLOCKS
  initial
  begin
    head_rl = 3'h2;
    stack_0_rl = 129'h0AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA;
    stack_1_rl = 129'h0AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA;
    stack_2_rl = 129'h0AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA;
    stack_3_rl = 129'h0AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA;
    stack_4_rl = 129'h0AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA;
    stack_5_rl = 129'h0AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA;
    stack_6_rl = 129'h0AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA;
    stack_7_rl = 129'h0AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA;
  end
  `endif // BSV_NO_INITIAL_BLOCKS
  // synopsys translate_on
endmodule  // mkRas


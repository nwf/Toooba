//
// Generated by Bluespec Compiler, version 2019.05.beta2 (build a88bf40db, 2019-05-24)
//
// On Mon Jul 13 18:49:44 BST 2020
//
//
// Ports:
// Name                         I/O  size props
// pred_0_pred                    O    25
// RDY_pred_0_pred                O     1 const
// pred_1_pred                    O    25
// RDY_pred_1_pred                O     1 const
// RDY_update                     O     1 const
// RDY_flush                      O     1 const
// flush_done                     O     1 const
// RDY_flush_done                 O     1 const
// CLK                            I     1 clock
// RST_N                          I     1 reset
// pred_0_pred_pc                 I   129
// pred_1_pred_pc                 I   129
// update_pc                      I   129
// update_taken                   I     1
// update_train                   I    24
// update_mispred                 I     1
// EN_update                      I     1
// EN_flush                       I     1 unused
// EN_pred_0_pred                 I     1
// EN_pred_1_pred                 I     1
//
// Combinational paths from inputs to outputs:
//   EN_pred_0_pred -> pred_1_pred
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

module mkTourPred(CLK,
		  RST_N,

		  pred_0_pred_pc,
		  EN_pred_0_pred,
		  pred_0_pred,
		  RDY_pred_0_pred,

		  pred_1_pred_pc,
		  EN_pred_1_pred,
		  pred_1_pred,
		  RDY_pred_1_pred,

		  update_pc,
		  update_taken,
		  update_train,
		  update_mispred,
		  EN_update,
		  RDY_update,

		  EN_flush,
		  RDY_flush,

		  flush_done,
		  RDY_flush_done);
  input  CLK;
  input  RST_N;

  // actionvalue method pred_0_pred
  input  [128 : 0] pred_0_pred_pc;
  input  EN_pred_0_pred;
  output [24 : 0] pred_0_pred;
  output RDY_pred_0_pred;

  // actionvalue method pred_1_pred
  input  [128 : 0] pred_1_pred_pc;
  input  EN_pred_1_pred;
  output [24 : 0] pred_1_pred;
  output RDY_pred_1_pred;

  // action method update
  input  [128 : 0] update_pc;
  input  update_taken;
  input  [23 : 0] update_train;
  input  update_mispred;
  input  EN_update;
  output RDY_update;

  // action method flush
  input  EN_flush;
  output RDY_flush;

  // value method flush_done
  output flush_done;
  output RDY_flush_done;

  // signals for module outputs
  wire [24 : 0] pred_0_pred, pred_1_pred;
  wire RDY_flush,
       RDY_flush_done,
       RDY_pred_0_pred,
       RDY_pred_1_pred,
       RDY_update,
       flush_done;

  // inlined wires
  wire [1 : 0] predCnt_lat_0$wget,
	       predCnt_lat_1$wget,
	       predRes_lat_0$wget,
	       predRes_lat_1$wget;

  // register predCnt_rl
  reg [1 : 0] predCnt_rl;
  wire [1 : 0] predCnt_rl$D_IN;
  wire predCnt_rl$EN;

  // register predRes_rl
  reg [1 : 0] predRes_rl;
  wire [1 : 0] predRes_rl$D_IN;
  wire predRes_rl$EN;

  // ports of submodule choiceBht
  wire [11 : 0] choiceBht$ADDR_1,
		choiceBht$ADDR_2,
		choiceBht$ADDR_3,
		choiceBht$ADDR_4,
		choiceBht$ADDR_5,
		choiceBht$ADDR_IN;
  wire [1 : 0] choiceBht$D_IN,
	       choiceBht$D_OUT_1,
	       choiceBht$D_OUT_2,
	       choiceBht$D_OUT_3;
  wire choiceBht$WE;

  // ports of submodule gHistReg
  wire [11 : 0] gHistReg$history, gHistReg$redirect_newHist;
  wire [1 : 0] gHistReg$addHistory_num, gHistReg$addHistory_taken;
  wire gHistReg$EN_addHistory, gHistReg$EN_redirect;

  // ports of submodule globalBht
  wire [11 : 0] globalBht$ADDR_1,
		globalBht$ADDR_2,
		globalBht$ADDR_3,
		globalBht$ADDR_4,
		globalBht$ADDR_5,
		globalBht$ADDR_IN;
  wire [1 : 0] globalBht$D_IN,
	       globalBht$D_OUT_1,
	       globalBht$D_OUT_2,
	       globalBht$D_OUT_3;
  wire globalBht$WE;

  // ports of submodule localBht
  wire [9 : 0] localBht$ADDR_1,
	       localBht$ADDR_2,
	       localBht$ADDR_3,
	       localBht$ADDR_4,
	       localBht$ADDR_5,
	       localBht$ADDR_IN;
  wire [2 : 0] localBht$D_IN,
	       localBht$D_OUT_1,
	       localBht$D_OUT_2,
	       localBht$D_OUT_3;
  wire localBht$WE;

  // ports of submodule localHistTab
  wire [9 : 0] localHistTab$ADDR_1,
	       localHistTab$ADDR_2,
	       localHistTab$ADDR_3,
	       localHistTab$ADDR_4,
	       localHistTab$ADDR_5,
	       localHistTab$ADDR_IN,
	       localHistTab$D_IN,
	       localHistTab$D_OUT_1,
	       localHistTab$D_OUT_2;
  wire localHistTab$WE;

  // rule scheduling signals
  wire CAN_FIRE_RL_canonGlobalHist,
       CAN_FIRE_RL_predCnt_canon,
       CAN_FIRE_RL_predRes_canon,
       CAN_FIRE_flush,
       CAN_FIRE_pred_0_pred,
       CAN_FIRE_pred_1_pred,
       CAN_FIRE_update,
       WILL_FIRE_RL_canonGlobalHist,
       WILL_FIRE_RL_predCnt_canon,
       WILL_FIRE_RL_predRes_canon,
       WILL_FIRE_flush,
       WILL_FIRE_pred_0_pred,
       WILL_FIRE_pred_1_pred,
       WILL_FIRE_update;

  // remaining internal signals
  wire [11 : 0] globalHist__h2457, globalHist__h2811;
  wire [1 : 0] IF_predCnt_lat_0_whas_THEN_predCnt_lat_0_wget__ETC___d8,
	       IF_predRes_lat_0_whas__5_THEN_predRes_lat_0_wg_ETC___d18,
	       upd__h2081,
	       upd__h2201,
	       upd__h2893,
	       upd__h3108,
	       x__h2572,
	       x__h2954,
	       y__h2774,
	       y__h3141;
  wire IF_choiceBht_sub_gHistReg_history__2_SRL_IF_pr_ETC___d49,
       IF_choiceBht_sub_gHistReg_history__2_SRL_predC_ETC___d32;

  // actionvalue method pred_0_pred
  assign pred_0_pred =
	     { IF_choiceBht_sub_gHistReg_history__2_SRL_predC_ETC___d32,
	       globalHist__h2457,
	       localHistTab$D_OUT_2,
	       globalBht$D_OUT_2[1],
	       localBht$D_OUT_3[2] } ;
  assign RDY_pred_0_pred = 1'd1 ;
  assign CAN_FIRE_pred_0_pred = 1'd1 ;
  assign WILL_FIRE_pred_0_pred = EN_pred_0_pred ;

  // actionvalue method pred_1_pred
  assign pred_1_pred =
	     { IF_choiceBht_sub_gHistReg_history__2_SRL_IF_pr_ETC___d49,
	       globalHist__h2811,
	       localHistTab$D_OUT_1,
	       globalBht$D_OUT_1[1],
	       localBht$D_OUT_2[2] } ;
  assign RDY_pred_1_pred = 1'd1 ;
  assign CAN_FIRE_pred_1_pred = 1'd1 ;
  assign WILL_FIRE_pred_1_pred = EN_pred_1_pred ;

  // action method update
  assign RDY_update = 1'd1 ;
  assign CAN_FIRE_update = 1'd1 ;
  assign WILL_FIRE_update = EN_update ;

  // action method flush
  assign RDY_flush = 1'd1 ;
  assign CAN_FIRE_flush = 1'd1 ;
  assign WILL_FIRE_flush = EN_flush ;

  // value method flush_done
  assign flush_done = 1'd1 ;
  assign RDY_flush_done = 1'd1 ;

  // submodule choiceBht
  RegFile #(.addr_width(32'd12),
	    .data_width(32'd2),
	    .lo(12'd0),
	    .hi(12'd4095)) choiceBht(.CLK(CLK),
				     .ADDR_1(choiceBht$ADDR_1),
				     .ADDR_2(choiceBht$ADDR_2),
				     .ADDR_3(choiceBht$ADDR_3),
				     .ADDR_4(choiceBht$ADDR_4),
				     .ADDR_5(choiceBht$ADDR_5),
				     .ADDR_IN(choiceBht$ADDR_IN),
				     .D_IN(choiceBht$D_IN),
				     .WE(choiceBht$WE),
				     .D_OUT_1(choiceBht$D_OUT_1),
				     .D_OUT_2(choiceBht$D_OUT_2),
				     .D_OUT_3(choiceBht$D_OUT_3),
				     .D_OUT_4(),
				     .D_OUT_5());

  // submodule gHistReg
  mkTourGHistReg gHistReg(.CLK(CLK),
			  .RST_N(RST_N),
			  .addHistory_num(gHistReg$addHistory_num),
			  .addHistory_taken(gHistReg$addHistory_taken),
			  .redirect_newHist(gHistReg$redirect_newHist),
			  .EN_addHistory(gHistReg$EN_addHistory),
			  .EN_redirect(gHistReg$EN_redirect),
			  .history(gHistReg$history),
			  .RDY_history(),
			  .RDY_addHistory(),
			  .RDY_redirect());

  // submodule globalBht
  RegFile #(.addr_width(32'd12),
	    .data_width(32'd2),
	    .lo(12'd0),
	    .hi(12'd4095)) globalBht(.CLK(CLK),
				     .ADDR_1(globalBht$ADDR_1),
				     .ADDR_2(globalBht$ADDR_2),
				     .ADDR_3(globalBht$ADDR_3),
				     .ADDR_4(globalBht$ADDR_4),
				     .ADDR_5(globalBht$ADDR_5),
				     .ADDR_IN(globalBht$ADDR_IN),
				     .D_IN(globalBht$D_IN),
				     .WE(globalBht$WE),
				     .D_OUT_1(globalBht$D_OUT_1),
				     .D_OUT_2(globalBht$D_OUT_2),
				     .D_OUT_3(globalBht$D_OUT_3),
				     .D_OUT_4(),
				     .D_OUT_5());

  // submodule localBht
  RegFile #(.addr_width(32'd10),
	    .data_width(32'd3),
	    .lo(10'd0),
	    .hi(10'd1023)) localBht(.CLK(CLK),
				    .ADDR_1(localBht$ADDR_1),
				    .ADDR_2(localBht$ADDR_2),
				    .ADDR_3(localBht$ADDR_3),
				    .ADDR_4(localBht$ADDR_4),
				    .ADDR_5(localBht$ADDR_5),
				    .ADDR_IN(localBht$ADDR_IN),
				    .D_IN(localBht$D_IN),
				    .WE(localBht$WE),
				    .D_OUT_1(localBht$D_OUT_1),
				    .D_OUT_2(localBht$D_OUT_2),
				    .D_OUT_3(localBht$D_OUT_3),
				    .D_OUT_4(),
				    .D_OUT_5());

  // submodule localHistTab
  RegFile #(.addr_width(32'd10),
	    .data_width(32'd10),
	    .lo(10'd0),
	    .hi(10'd1023)) localHistTab(.CLK(CLK),
					.ADDR_1(localHistTab$ADDR_1),
					.ADDR_2(localHistTab$ADDR_2),
					.ADDR_3(localHistTab$ADDR_3),
					.ADDR_4(localHistTab$ADDR_4),
					.ADDR_5(localHistTab$ADDR_5),
					.ADDR_IN(localHistTab$ADDR_IN),
					.D_IN(localHistTab$D_IN),
					.WE(localHistTab$WE),
					.D_OUT_1(localHistTab$D_OUT_1),
					.D_OUT_2(localHistTab$D_OUT_2),
					.D_OUT_3(),
					.D_OUT_4(),
					.D_OUT_5());

  // rule RL_canonGlobalHist
  assign CAN_FIRE_RL_canonGlobalHist = 1'd1 ;
  assign WILL_FIRE_RL_canonGlobalHist = 1'd1 ;

  // rule RL_predCnt_canon
  assign CAN_FIRE_RL_predCnt_canon = 1'd1 ;
  assign WILL_FIRE_RL_predCnt_canon = 1'd1 ;

  // rule RL_predRes_canon
  assign CAN_FIRE_RL_predRes_canon = 1'd1 ;
  assign WILL_FIRE_RL_predRes_canon = 1'd1 ;

  // inlined wires
  assign predCnt_lat_0$wget = predCnt_rl + 2'd1 ;
  assign predCnt_lat_1$wget =
	     IF_predCnt_lat_0_whas_THEN_predCnt_lat_0_wget__ETC___d8 + 2'd1 ;
  assign predRes_lat_0$wget =
	     IF_choiceBht_sub_gHistReg_history__2_SRL_predC_ETC___d32 ?
	       predRes_rl | x__h2572 :
	       predRes_rl & y__h2774 ;
  assign predRes_lat_1$wget =
	     IF_choiceBht_sub_gHistReg_history__2_SRL_IF_pr_ETC___d49 ?
	       IF_predRes_lat_0_whas__5_THEN_predRes_lat_0_wg_ETC___d18 |
	       x__h2954 :
	       IF_predRes_lat_0_whas__5_THEN_predRes_lat_0_wg_ETC___d18 &
	       y__h3141 ;

  // register predCnt_rl
  assign predCnt_rl$D_IN = 2'd0 ;
  assign predCnt_rl$EN = 1'd1 ;

  // register predRes_rl
  assign predRes_rl$D_IN = 2'd0 ;
  assign predRes_rl$EN = 1'd1 ;

  // submodule choiceBht
  assign choiceBht$ADDR_1 = globalHist__h2811 ;
  assign choiceBht$ADDR_2 = globalHist__h2457 ;
  assign choiceBht$ADDR_3 = update_train[23:12] ;
  assign choiceBht$ADDR_4 = 12'h0 ;
  assign choiceBht$ADDR_5 = 12'h0 ;
  assign choiceBht$ADDR_IN = update_train[23:12] ;
  assign choiceBht$D_IN =
	     (update_train[0] == update_taken) ?
	       ((choiceBht$D_OUT_3 == 2'd3) ?
		  choiceBht$D_OUT_3 :
		  choiceBht$D_OUT_3 + 2'd1) :
	       ((choiceBht$D_OUT_3 == 2'd0) ?
		  choiceBht$D_OUT_3 :
		  choiceBht$D_OUT_3 - 2'd1) ;
  assign choiceBht$WE = EN_update && update_train[1] != update_train[0] ;

  // submodule gHistReg
  assign gHistReg$addHistory_num =
	     EN_pred_1_pred ?
	       upd__h2201 :
	       IF_predCnt_lat_0_whas_THEN_predCnt_lat_0_wget__ETC___d8 ;
  assign gHistReg$addHistory_taken =
	     EN_pred_1_pred ?
	       upd__h2081 :
	       IF_predRes_lat_0_whas__5_THEN_predRes_lat_0_wg_ETC___d18 ;
  assign gHistReg$redirect_newHist = { update_taken, update_train[23:13] } ;
  assign gHistReg$EN_addHistory = 1'd1 ;
  assign gHistReg$EN_redirect = EN_update && update_mispred ;

  // submodule globalBht
  assign globalBht$ADDR_1 = globalHist__h2811 ;
  assign globalBht$ADDR_2 = globalHist__h2457 ;
  assign globalBht$ADDR_3 = update_train[23:12] ;
  assign globalBht$ADDR_4 = 12'h0 ;
  assign globalBht$ADDR_5 = 12'h0 ;
  assign globalBht$ADDR_IN = update_train[23:12] ;
  assign globalBht$D_IN =
	     update_taken ?
	       ((globalBht$D_OUT_3 == 2'd3) ?
		  globalBht$D_OUT_3 :
		  globalBht$D_OUT_3 + 2'd1) :
	       ((globalBht$D_OUT_3 == 2'd0) ?
		  globalBht$D_OUT_3 :
		  globalBht$D_OUT_3 - 2'd1) ;
  assign globalBht$WE = EN_update ;

  // submodule localBht
  assign localBht$ADDR_1 = update_train[11:2] ;
  assign localBht$ADDR_2 = localHistTab$D_OUT_1 ;
  assign localBht$ADDR_3 = localHistTab$D_OUT_2 ;
  assign localBht$ADDR_4 = 10'h0 ;
  assign localBht$ADDR_5 = 10'h0 ;
  assign localBht$ADDR_IN = update_train[11:2] ;
  assign localBht$D_IN =
	     update_taken ?
	       ((localBht$D_OUT_1 == 3'd7) ?
		  localBht$D_OUT_1 :
		  localBht$D_OUT_1 + 3'd1) :
	       ((localBht$D_OUT_1 == 3'd0) ?
		  localBht$D_OUT_1 :
		  localBht$D_OUT_1 - 3'd1) ;
  assign localBht$WE = EN_update ;

  // submodule localHistTab
  assign localHistTab$ADDR_1 = pred_1_pred_pc[11:2] ;
  assign localHistTab$ADDR_2 = pred_0_pred_pc[11:2] ;
  assign localHistTab$ADDR_3 = 10'h0 ;
  assign localHistTab$ADDR_4 = 10'h0 ;
  assign localHistTab$ADDR_5 = 10'h0 ;
  assign localHistTab$ADDR_IN = update_pc[11:2] ;
  assign localHistTab$D_IN = { update_taken, update_train[11:3] } ;
  assign localHistTab$WE = EN_update ;

  // remaining internal signals
  assign IF_choiceBht_sub_gHistReg_history__2_SRL_IF_pr_ETC___d49 =
	     choiceBht$D_OUT_1[1] ?
	       localBht$D_OUT_2[2] :
	       globalBht$D_OUT_1[1] ;
  assign IF_choiceBht_sub_gHistReg_history__2_SRL_predC_ETC___d32 =
	     choiceBht$D_OUT_2[1] ?
	       localBht$D_OUT_3[2] :
	       globalBht$D_OUT_2[1] ;
  assign IF_predCnt_lat_0_whas_THEN_predCnt_lat_0_wget__ETC___d8 =
	     EN_pred_0_pred ? upd__h2893 : predCnt_rl ;
  assign IF_predRes_lat_0_whas__5_THEN_predRes_lat_0_wg_ETC___d18 =
	     EN_pred_0_pred ? upd__h3108 : predRes_rl ;
  assign globalHist__h2457 = gHistReg$history >> predCnt_rl ;
  assign globalHist__h2811 =
	     gHistReg$history >>
	     IF_predCnt_lat_0_whas_THEN_predCnt_lat_0_wget__ETC___d8 ;
  assign upd__h2081 = predRes_lat_1$wget ;
  assign upd__h2201 = predCnt_lat_1$wget ;
  assign upd__h2893 = predCnt_lat_0$wget ;
  assign upd__h3108 = predRes_lat_0$wget ;
  assign x__h2572 = 2'd1 << predCnt_rl ;
  assign x__h2954 =
	     2'd1 << IF_predCnt_lat_0_whas_THEN_predCnt_lat_0_wget__ETC___d8 ;
  assign y__h2774 = ~x__h2572 ;
  assign y__h3141 = ~x__h2954 ;

  // handling of inlined registers

  always@(posedge CLK)
  begin
    if (RST_N == `BSV_RESET_VALUE)
      begin
        predCnt_rl <= `BSV_ASSIGNMENT_DELAY 2'd0;
	predRes_rl <= `BSV_ASSIGNMENT_DELAY 2'd0;
      end
    else
      begin
        if (predCnt_rl$EN)
	  predCnt_rl <= `BSV_ASSIGNMENT_DELAY predCnt_rl$D_IN;
	if (predRes_rl$EN)
	  predRes_rl <= `BSV_ASSIGNMENT_DELAY predRes_rl$D_IN;
      end
  end

  // synopsys translate_off
  `ifdef BSV_NO_INITIAL_BLOCKS
  `else // not BSV_NO_INITIAL_BLOCKS
  initial
  begin
    predCnt_rl = 2'h2;
    predRes_rl = 2'h2;
  end
  `endif // BSV_NO_INITIAL_BLOCKS
  // synopsys translate_on
endmodule  // mkTourPred


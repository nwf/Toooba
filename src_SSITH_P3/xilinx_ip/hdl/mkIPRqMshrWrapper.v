//
// Generated by Bluespec Compiler, version 2019.05.beta2 (build a88bf40db, 2019-05-24)
//
// On Sat Jul 18 16:20:41 BST 2020
//
//
// Ports:
// Name                         I/O  size props
// getEmptyEntryInit              O     2 reg
// RDY_getEmptyEntryInit          O     1
// sendRsToP_pRq_getRq            O    66
// RDY_sendRsToP_pRq_getRq        O     1 const
// RDY_sendRsToP_pRq_releaseEntry  O     1
// pipelineResp_getRq             O    66
// RDY_pipelineResp_getRq         O     1 const
// RDY_pipelineResp_releaseEntry  O     1
// RDY_pipelineResp_setDone       O     1 const
// stuck_get                      O    68
// RDY_stuck_get                  O     1 const
// CLK                            I     1 clock
// RST_N                          I     1 reset
// getEmptyEntryInit_r            I    66
// sendRsToP_pRq_getRq_n          I     2
// sendRsToP_pRq_releaseEntry_n   I     2
// pipelineResp_getRq_n           I     2
// pipelineResp_releaseEntry_n    I     2
// pipelineResp_setDone_n         I     2
// EN_sendRsToP_pRq_releaseEntry  I     1
// EN_pipelineResp_releaseEntry   I     1
// EN_pipelineResp_setDone        I     1
// EN_getEmptyEntryInit           I     1
// EN_stuck_get                   I     1 unused
//
// Combinational paths from inputs to outputs:
//   sendRsToP_pRq_getRq_n -> sendRsToP_pRq_getRq
//   pipelineResp_getRq_n -> pipelineResp_getRq
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

module mkIPRqMshrWrapper(CLK,
			 RST_N,

			 getEmptyEntryInit_r,
			 EN_getEmptyEntryInit,
			 getEmptyEntryInit,
			 RDY_getEmptyEntryInit,

			 sendRsToP_pRq_getRq_n,
			 sendRsToP_pRq_getRq,
			 RDY_sendRsToP_pRq_getRq,

			 sendRsToP_pRq_releaseEntry_n,
			 EN_sendRsToP_pRq_releaseEntry,
			 RDY_sendRsToP_pRq_releaseEntry,

			 pipelineResp_getRq_n,
			 pipelineResp_getRq,
			 RDY_pipelineResp_getRq,

			 pipelineResp_releaseEntry_n,
			 EN_pipelineResp_releaseEntry,
			 RDY_pipelineResp_releaseEntry,

			 pipelineResp_setDone_n,
			 EN_pipelineResp_setDone,
			 RDY_pipelineResp_setDone,

			 EN_stuck_get,
			 stuck_get,
			 RDY_stuck_get);
  input  CLK;
  input  RST_N;

  // actionvalue method getEmptyEntryInit
  input  [65 : 0] getEmptyEntryInit_r;
  input  EN_getEmptyEntryInit;
  output [1 : 0] getEmptyEntryInit;
  output RDY_getEmptyEntryInit;

  // value method sendRsToP_pRq_getRq
  input  [1 : 0] sendRsToP_pRq_getRq_n;
  output [65 : 0] sendRsToP_pRq_getRq;
  output RDY_sendRsToP_pRq_getRq;

  // action method sendRsToP_pRq_releaseEntry
  input  [1 : 0] sendRsToP_pRq_releaseEntry_n;
  input  EN_sendRsToP_pRq_releaseEntry;
  output RDY_sendRsToP_pRq_releaseEntry;

  // value method pipelineResp_getRq
  input  [1 : 0] pipelineResp_getRq_n;
  output [65 : 0] pipelineResp_getRq;
  output RDY_pipelineResp_getRq;

  // action method pipelineResp_releaseEntry
  input  [1 : 0] pipelineResp_releaseEntry_n;
  input  EN_pipelineResp_releaseEntry;
  output RDY_pipelineResp_releaseEntry;

  // action method pipelineResp_setDone
  input  [1 : 0] pipelineResp_setDone_n;
  input  EN_pipelineResp_setDone;
  output RDY_pipelineResp_setDone;

  // actionvalue method stuck_get
  input  EN_stuck_get;
  output [67 : 0] stuck_get;
  output RDY_stuck_get;

  // signals for module outputs
  wire [67 : 0] stuck_get;
  wire [65 : 0] pipelineResp_getRq, sendRsToP_pRq_getRq;
  wire [1 : 0] getEmptyEntryInit;
  wire RDY_getEmptyEntryInit,
       RDY_pipelineResp_getRq,
       RDY_pipelineResp_releaseEntry,
       RDY_pipelineResp_setDone,
       RDY_sendRsToP_pRq_getRq,
       RDY_sendRsToP_pRq_releaseEntry,
       RDY_stuck_get;

  // inlined wires
  wire [1 : 0] m_m_stateVec_0_lat_0$wget,
	       m_m_stateVec_1_lat_0$wget,
	       m_m_stateVec_2_lat_0$wget,
	       m_m_stateVec_3_lat_0$wget;
  wire m_m_stateVec_0_lat_0$whas,
       m_m_stateVec_0_lat_1$whas,
       m_m_stateVec_0_lat_2$whas,
       m_m_stateVec_1_lat_0$whas,
       m_m_stateVec_1_lat_1$whas,
       m_m_stateVec_1_lat_2$whas,
       m_m_stateVec_2_lat_0$whas,
       m_m_stateVec_2_lat_1$whas,
       m_m_stateVec_2_lat_2$whas,
       m_m_stateVec_3_lat_0$whas,
       m_m_stateVec_3_lat_1$whas,
       m_m_stateVec_3_lat_2$whas;

  // register m_m_initIdx
  reg [1 : 0] m_m_initIdx;
  wire [1 : 0] m_m_initIdx$D_IN;
  wire m_m_initIdx$EN;

  // register m_m_inited
  reg m_m_inited;
  wire m_m_inited$D_IN, m_m_inited$EN;

  // register m_m_releaseEntryQ_pipelineResp_data_0_rl
  reg [1 : 0] m_m_releaseEntryQ_pipelineResp_data_0_rl;
  wire [1 : 0] m_m_releaseEntryQ_pipelineResp_data_0_rl$D_IN;
  wire m_m_releaseEntryQ_pipelineResp_data_0_rl$EN;

  // register m_m_releaseEntryQ_pipelineResp_empty_rl
  reg m_m_releaseEntryQ_pipelineResp_empty_rl;
  wire m_m_releaseEntryQ_pipelineResp_empty_rl$D_IN,
       m_m_releaseEntryQ_pipelineResp_empty_rl$EN;

  // register m_m_releaseEntryQ_pipelineResp_full_rl
  reg m_m_releaseEntryQ_pipelineResp_full_rl;
  wire m_m_releaseEntryQ_pipelineResp_full_rl$D_IN,
       m_m_releaseEntryQ_pipelineResp_full_rl$EN;

  // register m_m_releaseEntryQ_sendRsToP_pRq_data_0_rl
  reg [1 : 0] m_m_releaseEntryQ_sendRsToP_pRq_data_0_rl;
  wire [1 : 0] m_m_releaseEntryQ_sendRsToP_pRq_data_0_rl$D_IN;
  wire m_m_releaseEntryQ_sendRsToP_pRq_data_0_rl$EN;

  // register m_m_releaseEntryQ_sendRsToP_pRq_empty_rl
  reg m_m_releaseEntryQ_sendRsToP_pRq_empty_rl;
  wire m_m_releaseEntryQ_sendRsToP_pRq_empty_rl$D_IN,
       m_m_releaseEntryQ_sendRsToP_pRq_empty_rl$EN;

  // register m_m_releaseEntryQ_sendRsToP_pRq_full_rl
  reg m_m_releaseEntryQ_sendRsToP_pRq_full_rl;
  wire m_m_releaseEntryQ_sendRsToP_pRq_full_rl$D_IN,
       m_m_releaseEntryQ_sendRsToP_pRq_full_rl$EN;

  // register m_m_reqVec_0_rl
  reg [65 : 0] m_m_reqVec_0_rl;
  wire [65 : 0] m_m_reqVec_0_rl$D_IN;
  wire m_m_reqVec_0_rl$EN;

  // register m_m_reqVec_1_rl
  reg [65 : 0] m_m_reqVec_1_rl;
  wire [65 : 0] m_m_reqVec_1_rl$D_IN;
  wire m_m_reqVec_1_rl$EN;

  // register m_m_reqVec_2_rl
  reg [65 : 0] m_m_reqVec_2_rl;
  wire [65 : 0] m_m_reqVec_2_rl$D_IN;
  wire m_m_reqVec_2_rl$EN;

  // register m_m_reqVec_3_rl
  reg [65 : 0] m_m_reqVec_3_rl;
  wire [65 : 0] m_m_reqVec_3_rl$D_IN;
  wire m_m_reqVec_3_rl$EN;

  // register m_m_stateVec_0_rl
  reg [1 : 0] m_m_stateVec_0_rl;
  wire [1 : 0] m_m_stateVec_0_rl$D_IN;
  wire m_m_stateVec_0_rl$EN;

  // register m_m_stateVec_1_rl
  reg [1 : 0] m_m_stateVec_1_rl;
  wire [1 : 0] m_m_stateVec_1_rl$D_IN;
  wire m_m_stateVec_1_rl$EN;

  // register m_m_stateVec_2_rl
  reg [1 : 0] m_m_stateVec_2_rl;
  wire [1 : 0] m_m_stateVec_2_rl$D_IN;
  wire m_m_stateVec_2_rl$EN;

  // register m_m_stateVec_3_rl
  reg [1 : 0] m_m_stateVec_3_rl;
  wire [1 : 0] m_m_stateVec_3_rl$D_IN;
  wire m_m_stateVec_3_rl$EN;

  // ports of submodule m_m_emptyEntryQ
  reg [1 : 0] m_m_emptyEntryQ$D_IN;
  wire [1 : 0] m_m_emptyEntryQ$D_OUT;
  wire m_m_emptyEntryQ$CLR,
       m_m_emptyEntryQ$DEQ,
       m_m_emptyEntryQ$EMPTY_N,
       m_m_emptyEntryQ$ENQ,
       m_m_emptyEntryQ$FULL_N;

  // rule scheduling signals
  wire CAN_FIRE_RL_m_m_doReleaseEntry_pipelineResp,
       CAN_FIRE_RL_m_m_doReleaseEntry_sendRsToP_pRq,
       CAN_FIRE_RL_m_m_initEmptyEntry,
       CAN_FIRE_RL_m_m_releaseEntryQ_pipelineResp_data_0_canon,
       CAN_FIRE_RL_m_m_releaseEntryQ_pipelineResp_empty_canon,
       CAN_FIRE_RL_m_m_releaseEntryQ_pipelineResp_full_canon,
       CAN_FIRE_RL_m_m_releaseEntryQ_sendRsToP_pRq_data_0_canon,
       CAN_FIRE_RL_m_m_releaseEntryQ_sendRsToP_pRq_empty_canon,
       CAN_FIRE_RL_m_m_releaseEntryQ_sendRsToP_pRq_full_canon,
       CAN_FIRE_RL_m_m_reqVec_0_canon,
       CAN_FIRE_RL_m_m_reqVec_1_canon,
       CAN_FIRE_RL_m_m_reqVec_2_canon,
       CAN_FIRE_RL_m_m_reqVec_3_canon,
       CAN_FIRE_RL_m_m_stateVec_0_canon,
       CAN_FIRE_RL_m_m_stateVec_1_canon,
       CAN_FIRE_RL_m_m_stateVec_2_canon,
       CAN_FIRE_RL_m_m_stateVec_3_canon,
       CAN_FIRE_getEmptyEntryInit,
       CAN_FIRE_pipelineResp_releaseEntry,
       CAN_FIRE_pipelineResp_setDone,
       CAN_FIRE_sendRsToP_pRq_releaseEntry,
       CAN_FIRE_stuck_get,
       WILL_FIRE_RL_m_m_doReleaseEntry_pipelineResp,
       WILL_FIRE_RL_m_m_doReleaseEntry_sendRsToP_pRq,
       WILL_FIRE_RL_m_m_initEmptyEntry,
       WILL_FIRE_RL_m_m_releaseEntryQ_pipelineResp_data_0_canon,
       WILL_FIRE_RL_m_m_releaseEntryQ_pipelineResp_empty_canon,
       WILL_FIRE_RL_m_m_releaseEntryQ_pipelineResp_full_canon,
       WILL_FIRE_RL_m_m_releaseEntryQ_sendRsToP_pRq_data_0_canon,
       WILL_FIRE_RL_m_m_releaseEntryQ_sendRsToP_pRq_empty_canon,
       WILL_FIRE_RL_m_m_releaseEntryQ_sendRsToP_pRq_full_canon,
       WILL_FIRE_RL_m_m_reqVec_0_canon,
       WILL_FIRE_RL_m_m_reqVec_1_canon,
       WILL_FIRE_RL_m_m_reqVec_2_canon,
       WILL_FIRE_RL_m_m_reqVec_3_canon,
       WILL_FIRE_RL_m_m_stateVec_0_canon,
       WILL_FIRE_RL_m_m_stateVec_1_canon,
       WILL_FIRE_RL_m_m_stateVec_2_canon,
       WILL_FIRE_RL_m_m_stateVec_3_canon,
       WILL_FIRE_getEmptyEntryInit,
       WILL_FIRE_pipelineResp_releaseEntry,
       WILL_FIRE_pipelineResp_setDone,
       WILL_FIRE_sendRsToP_pRq_releaseEntry,
       WILL_FIRE_stuck_get;

  // inputs to muxes for submodule ports
  wire [1 : 0] MUX_m_m_emptyEntryQ$enq_1__VAL_2,
	       MUX_m_m_emptyEntryQ$enq_1__VAL_3;
  wire MUX_m_m_emptyEntryQ$enq_1__SEL_2,
       MUX_m_m_stateVec_0_lat_0$wset_1__SEL_1,
       MUX_m_m_stateVec_1_lat_0$wset_1__SEL_1,
       MUX_m_m_stateVec_2_lat_0$wset_1__SEL_1,
       MUX_m_m_stateVec_3_lat_0$wset_1__SEL_1;

  // remaining internal signals
  reg [63 : 0] SEL_ARR_IF_m_m_reqVec_0_lat_0_whas__5_THEN_m_m_ETC___d171,
	       SEL_ARR_m_m_reqVec_0_rl_7_BITS_65_TO_2_59_m_m__ETC___d192;
  reg [1 : 0] SEL_ARR_IF_m_m_reqVec_0_lat_0_whas__5_THEN_m_m_ETC___d185,
	      SEL_ARR_m_m_reqVec_0_rl_7_BITS_1_TO_0_73_m_m_r_ETC___d194;
  wire [1 : 0] IF_m_m_stateVec_0_lat_1_whas_THEN_m_m_stateVec_ETC___d9,
	       IF_m_m_stateVec_1_lat_1_whas__3_THEN_m_m_state_ETC___d19,
	       IF_m_m_stateVec_2_lat_1_whas__3_THEN_m_m_state_ETC___d29,
	       IF_m_m_stateVec_3_lat_1_whas__3_THEN_m_m_state_ETC___d39,
	       v__h10232,
	       v__h9493;

  // actionvalue method getEmptyEntryInit
  assign getEmptyEntryInit = m_m_emptyEntryQ$D_OUT ;
  assign RDY_getEmptyEntryInit = m_m_inited && m_m_emptyEntryQ$EMPTY_N ;
  assign CAN_FIRE_getEmptyEntryInit = m_m_inited && m_m_emptyEntryQ$EMPTY_N ;
  assign WILL_FIRE_getEmptyEntryInit = EN_getEmptyEntryInit ;

  // value method sendRsToP_pRq_getRq
  assign sendRsToP_pRq_getRq =
	     { SEL_ARR_IF_m_m_reqVec_0_lat_0_whas__5_THEN_m_m_ETC___d171,
	       SEL_ARR_IF_m_m_reqVec_0_lat_0_whas__5_THEN_m_m_ETC___d185 } ;
  assign RDY_sendRsToP_pRq_getRq = 1'd1 ;

  // action method sendRsToP_pRq_releaseEntry
  assign RDY_sendRsToP_pRq_releaseEntry =
	     !m_m_releaseEntryQ_sendRsToP_pRq_full_rl && m_m_inited ;
  assign CAN_FIRE_sendRsToP_pRq_releaseEntry =
	     !m_m_releaseEntryQ_sendRsToP_pRq_full_rl && m_m_inited ;
  assign WILL_FIRE_sendRsToP_pRq_releaseEntry =
	     EN_sendRsToP_pRq_releaseEntry ;

  // value method pipelineResp_getRq
  assign pipelineResp_getRq =
	     { SEL_ARR_m_m_reqVec_0_rl_7_BITS_65_TO_2_59_m_m__ETC___d192,
	       SEL_ARR_m_m_reqVec_0_rl_7_BITS_1_TO_0_73_m_m_r_ETC___d194 } ;
  assign RDY_pipelineResp_getRq = 1'd1 ;

  // action method pipelineResp_releaseEntry
  assign RDY_pipelineResp_releaseEntry =
	     !m_m_releaseEntryQ_pipelineResp_full_rl && m_m_inited ;
  assign CAN_FIRE_pipelineResp_releaseEntry =
	     !m_m_releaseEntryQ_pipelineResp_full_rl && m_m_inited ;
  assign WILL_FIRE_pipelineResp_releaseEntry = EN_pipelineResp_releaseEntry ;

  // action method pipelineResp_setDone
  assign RDY_pipelineResp_setDone = 1'd1 ;
  assign CAN_FIRE_pipelineResp_setDone = 1'd1 ;
  assign WILL_FIRE_pipelineResp_setDone = EN_pipelineResp_setDone ;

  // actionvalue method stuck_get
  assign stuck_get =
	     68'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx /* unspecified value */  ;
  assign RDY_stuck_get = 1'd0 ;
  assign CAN_FIRE_stuck_get = 1'd0 ;
  assign WILL_FIRE_stuck_get = EN_stuck_get ;

  // submodule m_m_emptyEntryQ
  SizedFIFO #(.p1width(32'd2),
	      .p2depth(32'd4),
	      .p3cntr_width(32'd2),
	      .guarded(32'd1)) m_m_emptyEntryQ(.RST(RST_N),
					       .CLK(CLK),
					       .D_IN(m_m_emptyEntryQ$D_IN),
					       .ENQ(m_m_emptyEntryQ$ENQ),
					       .DEQ(m_m_emptyEntryQ$DEQ),
					       .CLR(m_m_emptyEntryQ$CLR),
					       .D_OUT(m_m_emptyEntryQ$D_OUT),
					       .FULL_N(m_m_emptyEntryQ$FULL_N),
					       .EMPTY_N(m_m_emptyEntryQ$EMPTY_N));

  // rule RL_m_m_initEmptyEntry
  assign CAN_FIRE_RL_m_m_initEmptyEntry =
	     m_m_emptyEntryQ$FULL_N && !m_m_inited ;
  assign WILL_FIRE_RL_m_m_initEmptyEntry = CAN_FIRE_RL_m_m_initEmptyEntry ;

  // rule RL_m_m_doReleaseEntry_sendRsToP_pRq
  assign CAN_FIRE_RL_m_m_doReleaseEntry_sendRsToP_pRq =
	     MUX_m_m_emptyEntryQ$enq_1__SEL_2 ;
  assign WILL_FIRE_RL_m_m_doReleaseEntry_sendRsToP_pRq =
	     MUX_m_m_emptyEntryQ$enq_1__SEL_2 ;

  // rule RL_m_m_doReleaseEntry_pipelineResp
  assign CAN_FIRE_RL_m_m_doReleaseEntry_pipelineResp =
	     (EN_pipelineResp_releaseEntry ||
	      !m_m_releaseEntryQ_pipelineResp_empty_rl) &&
	     m_m_emptyEntryQ$FULL_N &&
	     m_m_inited ;
  assign WILL_FIRE_RL_m_m_doReleaseEntry_pipelineResp =
	     CAN_FIRE_RL_m_m_doReleaseEntry_pipelineResp &&
	     !WILL_FIRE_RL_m_m_doReleaseEntry_sendRsToP_pRq ;

  // rule RL_m_m_stateVec_0_canon
  assign CAN_FIRE_RL_m_m_stateVec_0_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_stateVec_0_canon = 1'd1 ;

  // rule RL_m_m_stateVec_1_canon
  assign CAN_FIRE_RL_m_m_stateVec_1_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_stateVec_1_canon = 1'd1 ;

  // rule RL_m_m_stateVec_2_canon
  assign CAN_FIRE_RL_m_m_stateVec_2_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_stateVec_2_canon = 1'd1 ;

  // rule RL_m_m_stateVec_3_canon
  assign CAN_FIRE_RL_m_m_stateVec_3_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_stateVec_3_canon = 1'd1 ;

  // rule RL_m_m_reqVec_0_canon
  assign CAN_FIRE_RL_m_m_reqVec_0_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_reqVec_0_canon = 1'd1 ;

  // rule RL_m_m_reqVec_1_canon
  assign CAN_FIRE_RL_m_m_reqVec_1_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_reqVec_1_canon = 1'd1 ;

  // rule RL_m_m_reqVec_2_canon
  assign CAN_FIRE_RL_m_m_reqVec_2_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_reqVec_2_canon = 1'd1 ;

  // rule RL_m_m_reqVec_3_canon
  assign CAN_FIRE_RL_m_m_reqVec_3_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_reqVec_3_canon = 1'd1 ;

  // rule RL_m_m_releaseEntryQ_sendRsToP_pRq_data_0_canon
  assign CAN_FIRE_RL_m_m_releaseEntryQ_sendRsToP_pRq_data_0_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_releaseEntryQ_sendRsToP_pRq_data_0_canon = 1'd1 ;

  // rule RL_m_m_releaseEntryQ_sendRsToP_pRq_empty_canon
  assign CAN_FIRE_RL_m_m_releaseEntryQ_sendRsToP_pRq_empty_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_releaseEntryQ_sendRsToP_pRq_empty_canon = 1'd1 ;

  // rule RL_m_m_releaseEntryQ_sendRsToP_pRq_full_canon
  assign CAN_FIRE_RL_m_m_releaseEntryQ_sendRsToP_pRq_full_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_releaseEntryQ_sendRsToP_pRq_full_canon = 1'd1 ;

  // rule RL_m_m_releaseEntryQ_pipelineResp_data_0_canon
  assign CAN_FIRE_RL_m_m_releaseEntryQ_pipelineResp_data_0_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_releaseEntryQ_pipelineResp_data_0_canon = 1'd1 ;

  // rule RL_m_m_releaseEntryQ_pipelineResp_empty_canon
  assign CAN_FIRE_RL_m_m_releaseEntryQ_pipelineResp_empty_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_releaseEntryQ_pipelineResp_empty_canon = 1'd1 ;

  // rule RL_m_m_releaseEntryQ_pipelineResp_full_canon
  assign CAN_FIRE_RL_m_m_releaseEntryQ_pipelineResp_full_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_releaseEntryQ_pipelineResp_full_canon = 1'd1 ;

  // inputs to muxes for submodule ports
  assign MUX_m_m_emptyEntryQ$enq_1__SEL_2 =
	     (EN_sendRsToP_pRq_releaseEntry ||
	      !m_m_releaseEntryQ_sendRsToP_pRq_empty_rl) &&
	     m_m_emptyEntryQ$FULL_N &&
	     m_m_inited ;
  assign MUX_m_m_stateVec_0_lat_0$wset_1__SEL_1 =
	     EN_pipelineResp_releaseEntry &&
	     pipelineResp_releaseEntry_n == 2'd0 ;
  assign MUX_m_m_stateVec_1_lat_0$wset_1__SEL_1 =
	     EN_pipelineResp_releaseEntry &&
	     pipelineResp_releaseEntry_n == 2'd1 ;
  assign MUX_m_m_stateVec_2_lat_0$wset_1__SEL_1 =
	     EN_pipelineResp_releaseEntry &&
	     pipelineResp_releaseEntry_n == 2'd2 ;
  assign MUX_m_m_stateVec_3_lat_0$wset_1__SEL_1 =
	     EN_pipelineResp_releaseEntry &&
	     pipelineResp_releaseEntry_n == 2'd3 ;
  assign MUX_m_m_emptyEntryQ$enq_1__VAL_2 =
	     EN_sendRsToP_pRq_releaseEntry ?
	       sendRsToP_pRq_releaseEntry_n :
	       m_m_releaseEntryQ_sendRsToP_pRq_data_0_rl ;
  assign MUX_m_m_emptyEntryQ$enq_1__VAL_3 =
	     EN_pipelineResp_releaseEntry ?
	       pipelineResp_releaseEntry_n :
	       m_m_releaseEntryQ_pipelineResp_data_0_rl ;

  // inlined wires
  assign m_m_stateVec_0_lat_0$wget =
	     MUX_m_m_stateVec_0_lat_0$wset_1__SEL_1 ? 2'd0 : 2'd2 ;
  assign m_m_stateVec_0_lat_0$whas =
	     EN_pipelineResp_releaseEntry &&
	     pipelineResp_releaseEntry_n == 2'd0 ||
	     EN_pipelineResp_setDone && pipelineResp_setDone_n == 2'd0 ;
  assign m_m_stateVec_0_lat_1$whas =
	     EN_sendRsToP_pRq_releaseEntry &&
	     sendRsToP_pRq_releaseEntry_n == 2'd0 ;
  assign m_m_stateVec_0_lat_2$whas =
	     EN_getEmptyEntryInit && m_m_emptyEntryQ$D_OUT == 2'd0 ;
  assign m_m_stateVec_1_lat_0$wget =
	     MUX_m_m_stateVec_1_lat_0$wset_1__SEL_1 ? 2'd0 : 2'd2 ;
  assign m_m_stateVec_1_lat_0$whas =
	     EN_pipelineResp_releaseEntry &&
	     pipelineResp_releaseEntry_n == 2'd1 ||
	     EN_pipelineResp_setDone && pipelineResp_setDone_n == 2'd1 ;
  assign m_m_stateVec_1_lat_1$whas =
	     EN_sendRsToP_pRq_releaseEntry &&
	     sendRsToP_pRq_releaseEntry_n == 2'd1 ;
  assign m_m_stateVec_1_lat_2$whas =
	     EN_getEmptyEntryInit && m_m_emptyEntryQ$D_OUT == 2'd1 ;
  assign m_m_stateVec_2_lat_0$wget =
	     MUX_m_m_stateVec_2_lat_0$wset_1__SEL_1 ? 2'd0 : 2'd2 ;
  assign m_m_stateVec_2_lat_0$whas =
	     EN_pipelineResp_releaseEntry &&
	     pipelineResp_releaseEntry_n == 2'd2 ||
	     EN_pipelineResp_setDone && pipelineResp_setDone_n == 2'd2 ;
  assign m_m_stateVec_2_lat_1$whas =
	     EN_sendRsToP_pRq_releaseEntry &&
	     sendRsToP_pRq_releaseEntry_n == 2'd2 ;
  assign m_m_stateVec_2_lat_2$whas =
	     EN_getEmptyEntryInit && m_m_emptyEntryQ$D_OUT == 2'd2 ;
  assign m_m_stateVec_3_lat_0$wget =
	     MUX_m_m_stateVec_3_lat_0$wset_1__SEL_1 ? 2'd0 : 2'd2 ;
  assign m_m_stateVec_3_lat_0$whas =
	     EN_pipelineResp_releaseEntry &&
	     pipelineResp_releaseEntry_n == 2'd3 ||
	     EN_pipelineResp_setDone && pipelineResp_setDone_n == 2'd3 ;
  assign m_m_stateVec_3_lat_1$whas =
	     EN_sendRsToP_pRq_releaseEntry &&
	     sendRsToP_pRq_releaseEntry_n == 2'd3 ;
  assign m_m_stateVec_3_lat_2$whas =
	     EN_getEmptyEntryInit && m_m_emptyEntryQ$D_OUT == 2'd3 ;

  // register m_m_initIdx
  assign m_m_initIdx$D_IN = m_m_initIdx + 2'd1 ;
  assign m_m_initIdx$EN = CAN_FIRE_RL_m_m_initEmptyEntry ;

  // register m_m_inited
  assign m_m_inited$D_IN = 1'd1 ;
  assign m_m_inited$EN =
	     WILL_FIRE_RL_m_m_initEmptyEntry && m_m_initIdx == 2'd3 ;

  // register m_m_releaseEntryQ_pipelineResp_data_0_rl
  assign m_m_releaseEntryQ_pipelineResp_data_0_rl$D_IN = v__h10232 ;
  assign m_m_releaseEntryQ_pipelineResp_data_0_rl$EN = 1'd1 ;

  // register m_m_releaseEntryQ_pipelineResp_empty_rl
  assign m_m_releaseEntryQ_pipelineResp_empty_rl$D_IN =
	     WILL_FIRE_RL_m_m_doReleaseEntry_pipelineResp ||
	     !EN_pipelineResp_releaseEntry &&
	     m_m_releaseEntryQ_pipelineResp_empty_rl ;
  assign m_m_releaseEntryQ_pipelineResp_empty_rl$EN = 1'd1 ;

  // register m_m_releaseEntryQ_pipelineResp_full_rl
  assign m_m_releaseEntryQ_pipelineResp_full_rl$D_IN =
	     !WILL_FIRE_RL_m_m_doReleaseEntry_pipelineResp &&
	     (EN_pipelineResp_releaseEntry ||
	      m_m_releaseEntryQ_pipelineResp_full_rl) ;
  assign m_m_releaseEntryQ_pipelineResp_full_rl$EN = 1'd1 ;

  // register m_m_releaseEntryQ_sendRsToP_pRq_data_0_rl
  assign m_m_releaseEntryQ_sendRsToP_pRq_data_0_rl$D_IN = v__h9493 ;
  assign m_m_releaseEntryQ_sendRsToP_pRq_data_0_rl$EN = 1'd1 ;

  // register m_m_releaseEntryQ_sendRsToP_pRq_empty_rl
  assign m_m_releaseEntryQ_sendRsToP_pRq_empty_rl$D_IN =
	     MUX_m_m_emptyEntryQ$enq_1__SEL_2 ||
	     !EN_sendRsToP_pRq_releaseEntry &&
	     m_m_releaseEntryQ_sendRsToP_pRq_empty_rl ;
  assign m_m_releaseEntryQ_sendRsToP_pRq_empty_rl$EN = 1'd1 ;

  // register m_m_releaseEntryQ_sendRsToP_pRq_full_rl
  assign m_m_releaseEntryQ_sendRsToP_pRq_full_rl$D_IN =
	     !MUX_m_m_emptyEntryQ$enq_1__SEL_2 &&
	     (EN_sendRsToP_pRq_releaseEntry ||
	      m_m_releaseEntryQ_sendRsToP_pRq_full_rl) ;
  assign m_m_releaseEntryQ_sendRsToP_pRq_full_rl$EN = 1'd1 ;

  // register m_m_reqVec_0_rl
  assign m_m_reqVec_0_rl$D_IN =
	     m_m_stateVec_0_lat_2$whas ?
	       getEmptyEntryInit_r :
	       m_m_reqVec_0_rl ;
  assign m_m_reqVec_0_rl$EN = 1'd1 ;

  // register m_m_reqVec_1_rl
  assign m_m_reqVec_1_rl$D_IN =
	     m_m_stateVec_1_lat_2$whas ?
	       getEmptyEntryInit_r :
	       m_m_reqVec_1_rl ;
  assign m_m_reqVec_1_rl$EN = 1'd1 ;

  // register m_m_reqVec_2_rl
  assign m_m_reqVec_2_rl$D_IN =
	     m_m_stateVec_2_lat_2$whas ?
	       getEmptyEntryInit_r :
	       m_m_reqVec_2_rl ;
  assign m_m_reqVec_2_rl$EN = 1'd1 ;

  // register m_m_reqVec_3_rl
  assign m_m_reqVec_3_rl$D_IN =
	     m_m_stateVec_3_lat_2$whas ?
	       getEmptyEntryInit_r :
	       m_m_reqVec_3_rl ;
  assign m_m_reqVec_3_rl$EN = 1'd1 ;

  // register m_m_stateVec_0_rl
  assign m_m_stateVec_0_rl$D_IN =
	     m_m_stateVec_0_lat_2$whas ?
	       2'd1 :
	       IF_m_m_stateVec_0_lat_1_whas_THEN_m_m_stateVec_ETC___d9 ;
  assign m_m_stateVec_0_rl$EN = 1'd1 ;

  // register m_m_stateVec_1_rl
  assign m_m_stateVec_1_rl$D_IN =
	     m_m_stateVec_1_lat_2$whas ?
	       2'd1 :
	       IF_m_m_stateVec_1_lat_1_whas__3_THEN_m_m_state_ETC___d19 ;
  assign m_m_stateVec_1_rl$EN = 1'd1 ;

  // register m_m_stateVec_2_rl
  assign m_m_stateVec_2_rl$D_IN =
	     m_m_stateVec_2_lat_2$whas ?
	       2'd1 :
	       IF_m_m_stateVec_2_lat_1_whas__3_THEN_m_m_state_ETC___d29 ;
  assign m_m_stateVec_2_rl$EN = 1'd1 ;

  // register m_m_stateVec_3_rl
  assign m_m_stateVec_3_rl$D_IN =
	     m_m_stateVec_3_lat_2$whas ?
	       2'd1 :
	       IF_m_m_stateVec_3_lat_1_whas__3_THEN_m_m_state_ETC___d39 ;
  assign m_m_stateVec_3_rl$EN = 1'd1 ;

  // submodule m_m_emptyEntryQ
  always@(WILL_FIRE_RL_m_m_initEmptyEntry or
	  m_m_initIdx or
	  WILL_FIRE_RL_m_m_doReleaseEntry_sendRsToP_pRq or
	  MUX_m_m_emptyEntryQ$enq_1__VAL_2 or
	  WILL_FIRE_RL_m_m_doReleaseEntry_pipelineResp or
	  MUX_m_m_emptyEntryQ$enq_1__VAL_3)
  begin
    case (1'b1) // synopsys parallel_case
      WILL_FIRE_RL_m_m_initEmptyEntry: m_m_emptyEntryQ$D_IN = m_m_initIdx;
      WILL_FIRE_RL_m_m_doReleaseEntry_sendRsToP_pRq:
	  m_m_emptyEntryQ$D_IN = MUX_m_m_emptyEntryQ$enq_1__VAL_2;
      WILL_FIRE_RL_m_m_doReleaseEntry_pipelineResp:
	  m_m_emptyEntryQ$D_IN = MUX_m_m_emptyEntryQ$enq_1__VAL_3;
      default: m_m_emptyEntryQ$D_IN = 2'bxx /* unspecified value */ ;
    endcase
  end
  assign m_m_emptyEntryQ$ENQ =
	     WILL_FIRE_RL_m_m_initEmptyEntry ||
	     WILL_FIRE_RL_m_m_doReleaseEntry_sendRsToP_pRq ||
	     WILL_FIRE_RL_m_m_doReleaseEntry_pipelineResp ;
  assign m_m_emptyEntryQ$DEQ = EN_getEmptyEntryInit ;
  assign m_m_emptyEntryQ$CLR = 1'b0 ;

  // remaining internal signals
  assign IF_m_m_stateVec_0_lat_1_whas_THEN_m_m_stateVec_ETC___d9 =
	     m_m_stateVec_0_lat_1$whas ?
	       2'd0 :
	       (m_m_stateVec_0_lat_0$whas ?
		  m_m_stateVec_0_lat_0$wget :
		  m_m_stateVec_0_rl) ;
  assign IF_m_m_stateVec_1_lat_1_whas__3_THEN_m_m_state_ETC___d19 =
	     m_m_stateVec_1_lat_1$whas ?
	       2'd0 :
	       (m_m_stateVec_1_lat_0$whas ?
		  m_m_stateVec_1_lat_0$wget :
		  m_m_stateVec_1_rl) ;
  assign IF_m_m_stateVec_2_lat_1_whas__3_THEN_m_m_state_ETC___d29 =
	     m_m_stateVec_2_lat_1$whas ?
	       2'd0 :
	       (m_m_stateVec_2_lat_0$whas ?
		  m_m_stateVec_2_lat_0$wget :
		  m_m_stateVec_2_rl) ;
  assign IF_m_m_stateVec_3_lat_1_whas__3_THEN_m_m_state_ETC___d39 =
	     m_m_stateVec_3_lat_1$whas ?
	       2'd0 :
	       (m_m_stateVec_3_lat_0$whas ?
		  m_m_stateVec_3_lat_0$wget :
		  m_m_stateVec_3_rl) ;
  assign v__h10232 = MUX_m_m_emptyEntryQ$enq_1__VAL_3 ;
  assign v__h9493 = MUX_m_m_emptyEntryQ$enq_1__VAL_2 ;
  always@(sendRsToP_pRq_getRq_n or
	  m_m_reqVec_0_rl or
	  m_m_reqVec_1_rl or m_m_reqVec_2_rl or m_m_reqVec_3_rl)
  begin
    case (sendRsToP_pRq_getRq_n)
      2'd0:
	  SEL_ARR_IF_m_m_reqVec_0_lat_0_whas__5_THEN_m_m_ETC___d171 =
	      m_m_reqVec_0_rl[65:2];
      2'd1:
	  SEL_ARR_IF_m_m_reqVec_0_lat_0_whas__5_THEN_m_m_ETC___d171 =
	      m_m_reqVec_1_rl[65:2];
      2'd2:
	  SEL_ARR_IF_m_m_reqVec_0_lat_0_whas__5_THEN_m_m_ETC___d171 =
	      m_m_reqVec_2_rl[65:2];
      2'd3:
	  SEL_ARR_IF_m_m_reqVec_0_lat_0_whas__5_THEN_m_m_ETC___d171 =
	      m_m_reqVec_3_rl[65:2];
    endcase
  end
  always@(pipelineResp_getRq_n or
	  m_m_reqVec_0_rl or
	  m_m_reqVec_1_rl or m_m_reqVec_2_rl or m_m_reqVec_3_rl)
  begin
    case (pipelineResp_getRq_n)
      2'd0:
	  SEL_ARR_m_m_reqVec_0_rl_7_BITS_1_TO_0_73_m_m_r_ETC___d194 =
	      m_m_reqVec_0_rl[1:0];
      2'd1:
	  SEL_ARR_m_m_reqVec_0_rl_7_BITS_1_TO_0_73_m_m_r_ETC___d194 =
	      m_m_reqVec_1_rl[1:0];
      2'd2:
	  SEL_ARR_m_m_reqVec_0_rl_7_BITS_1_TO_0_73_m_m_r_ETC___d194 =
	      m_m_reqVec_2_rl[1:0];
      2'd3:
	  SEL_ARR_m_m_reqVec_0_rl_7_BITS_1_TO_0_73_m_m_r_ETC___d194 =
	      m_m_reqVec_3_rl[1:0];
    endcase
  end
  always@(sendRsToP_pRq_getRq_n or
	  m_m_reqVec_0_rl or
	  m_m_reqVec_1_rl or m_m_reqVec_2_rl or m_m_reqVec_3_rl)
  begin
    case (sendRsToP_pRq_getRq_n)
      2'd0:
	  SEL_ARR_IF_m_m_reqVec_0_lat_0_whas__5_THEN_m_m_ETC___d185 =
	      m_m_reqVec_0_rl[1:0];
      2'd1:
	  SEL_ARR_IF_m_m_reqVec_0_lat_0_whas__5_THEN_m_m_ETC___d185 =
	      m_m_reqVec_1_rl[1:0];
      2'd2:
	  SEL_ARR_IF_m_m_reqVec_0_lat_0_whas__5_THEN_m_m_ETC___d185 =
	      m_m_reqVec_2_rl[1:0];
      2'd3:
	  SEL_ARR_IF_m_m_reqVec_0_lat_0_whas__5_THEN_m_m_ETC___d185 =
	      m_m_reqVec_3_rl[1:0];
    endcase
  end
  always@(pipelineResp_getRq_n or
	  m_m_reqVec_0_rl or
	  m_m_reqVec_1_rl or m_m_reqVec_2_rl or m_m_reqVec_3_rl)
  begin
    case (pipelineResp_getRq_n)
      2'd0:
	  SEL_ARR_m_m_reqVec_0_rl_7_BITS_65_TO_2_59_m_m__ETC___d192 =
	      m_m_reqVec_0_rl[65:2];
      2'd1:
	  SEL_ARR_m_m_reqVec_0_rl_7_BITS_65_TO_2_59_m_m__ETC___d192 =
	      m_m_reqVec_1_rl[65:2];
      2'd2:
	  SEL_ARR_m_m_reqVec_0_rl_7_BITS_65_TO_2_59_m_m__ETC___d192 =
	      m_m_reqVec_2_rl[65:2];
      2'd3:
	  SEL_ARR_m_m_reqVec_0_rl_7_BITS_65_TO_2_59_m_m__ETC___d192 =
	      m_m_reqVec_3_rl[65:2];
    endcase
  end

  // handling of inlined registers

  always@(posedge CLK)
  begin
    if (RST_N == `BSV_RESET_VALUE)
      begin
        m_m_initIdx <= `BSV_ASSIGNMENT_DELAY 2'd0;
	m_m_inited <= `BSV_ASSIGNMENT_DELAY 1'd0;
	m_m_releaseEntryQ_pipelineResp_data_0_rl <= `BSV_ASSIGNMENT_DELAY
	    2'bxx /* unspecified value */ ;
	m_m_releaseEntryQ_pipelineResp_empty_rl <= `BSV_ASSIGNMENT_DELAY 1'd1;
	m_m_releaseEntryQ_pipelineResp_full_rl <= `BSV_ASSIGNMENT_DELAY 1'd0;
	m_m_releaseEntryQ_sendRsToP_pRq_data_0_rl <= `BSV_ASSIGNMENT_DELAY
	    2'bxx /* unspecified value */ ;
	m_m_releaseEntryQ_sendRsToP_pRq_empty_rl <= `BSV_ASSIGNMENT_DELAY
	    1'd1;
	m_m_releaseEntryQ_sendRsToP_pRq_full_rl <= `BSV_ASSIGNMENT_DELAY 1'd0;
	m_m_reqVec_0_rl <= `BSV_ASSIGNMENT_DELAY
	    66'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx /* unspecified value */ ;
	m_m_reqVec_1_rl <= `BSV_ASSIGNMENT_DELAY
	    66'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx /* unspecified value */ ;
	m_m_reqVec_2_rl <= `BSV_ASSIGNMENT_DELAY
	    66'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx /* unspecified value */ ;
	m_m_reqVec_3_rl <= `BSV_ASSIGNMENT_DELAY
	    66'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx /* unspecified value */ ;
	m_m_stateVec_0_rl <= `BSV_ASSIGNMENT_DELAY 2'd0;
	m_m_stateVec_1_rl <= `BSV_ASSIGNMENT_DELAY 2'd0;
	m_m_stateVec_2_rl <= `BSV_ASSIGNMENT_DELAY 2'd0;
	m_m_stateVec_3_rl <= `BSV_ASSIGNMENT_DELAY 2'd0;
      end
    else
      begin
        if (m_m_initIdx$EN)
	  m_m_initIdx <= `BSV_ASSIGNMENT_DELAY m_m_initIdx$D_IN;
	if (m_m_inited$EN)
	  m_m_inited <= `BSV_ASSIGNMENT_DELAY m_m_inited$D_IN;
	if (m_m_releaseEntryQ_pipelineResp_data_0_rl$EN)
	  m_m_releaseEntryQ_pipelineResp_data_0_rl <= `BSV_ASSIGNMENT_DELAY
	      m_m_releaseEntryQ_pipelineResp_data_0_rl$D_IN;
	if (m_m_releaseEntryQ_pipelineResp_empty_rl$EN)
	  m_m_releaseEntryQ_pipelineResp_empty_rl <= `BSV_ASSIGNMENT_DELAY
	      m_m_releaseEntryQ_pipelineResp_empty_rl$D_IN;
	if (m_m_releaseEntryQ_pipelineResp_full_rl$EN)
	  m_m_releaseEntryQ_pipelineResp_full_rl <= `BSV_ASSIGNMENT_DELAY
	      m_m_releaseEntryQ_pipelineResp_full_rl$D_IN;
	if (m_m_releaseEntryQ_sendRsToP_pRq_data_0_rl$EN)
	  m_m_releaseEntryQ_sendRsToP_pRq_data_0_rl <= `BSV_ASSIGNMENT_DELAY
	      m_m_releaseEntryQ_sendRsToP_pRq_data_0_rl$D_IN;
	if (m_m_releaseEntryQ_sendRsToP_pRq_empty_rl$EN)
	  m_m_releaseEntryQ_sendRsToP_pRq_empty_rl <= `BSV_ASSIGNMENT_DELAY
	      m_m_releaseEntryQ_sendRsToP_pRq_empty_rl$D_IN;
	if (m_m_releaseEntryQ_sendRsToP_pRq_full_rl$EN)
	  m_m_releaseEntryQ_sendRsToP_pRq_full_rl <= `BSV_ASSIGNMENT_DELAY
	      m_m_releaseEntryQ_sendRsToP_pRq_full_rl$D_IN;
	if (m_m_reqVec_0_rl$EN)
	  m_m_reqVec_0_rl <= `BSV_ASSIGNMENT_DELAY m_m_reqVec_0_rl$D_IN;
	if (m_m_reqVec_1_rl$EN)
	  m_m_reqVec_1_rl <= `BSV_ASSIGNMENT_DELAY m_m_reqVec_1_rl$D_IN;
	if (m_m_reqVec_2_rl$EN)
	  m_m_reqVec_2_rl <= `BSV_ASSIGNMENT_DELAY m_m_reqVec_2_rl$D_IN;
	if (m_m_reqVec_3_rl$EN)
	  m_m_reqVec_3_rl <= `BSV_ASSIGNMENT_DELAY m_m_reqVec_3_rl$D_IN;
	if (m_m_stateVec_0_rl$EN)
	  m_m_stateVec_0_rl <= `BSV_ASSIGNMENT_DELAY m_m_stateVec_0_rl$D_IN;
	if (m_m_stateVec_1_rl$EN)
	  m_m_stateVec_1_rl <= `BSV_ASSIGNMENT_DELAY m_m_stateVec_1_rl$D_IN;
	if (m_m_stateVec_2_rl$EN)
	  m_m_stateVec_2_rl <= `BSV_ASSIGNMENT_DELAY m_m_stateVec_2_rl$D_IN;
	if (m_m_stateVec_3_rl$EN)
	  m_m_stateVec_3_rl <= `BSV_ASSIGNMENT_DELAY m_m_stateVec_3_rl$D_IN;
      end
  end

  // synopsys translate_off
  `ifdef BSV_NO_INITIAL_BLOCKS
  `else // not BSV_NO_INITIAL_BLOCKS
  initial
  begin
    m_m_initIdx = 2'h2;
    m_m_inited = 1'h0;
    m_m_releaseEntryQ_pipelineResp_data_0_rl = 2'h2;
    m_m_releaseEntryQ_pipelineResp_empty_rl = 1'h0;
    m_m_releaseEntryQ_pipelineResp_full_rl = 1'h0;
    m_m_releaseEntryQ_sendRsToP_pRq_data_0_rl = 2'h2;
    m_m_releaseEntryQ_sendRsToP_pRq_empty_rl = 1'h0;
    m_m_releaseEntryQ_sendRsToP_pRq_full_rl = 1'h0;
    m_m_reqVec_0_rl = 66'h2AAAAAAAAAAAAAAAA;
    m_m_reqVec_1_rl = 66'h2AAAAAAAAAAAAAAAA;
    m_m_reqVec_2_rl = 66'h2AAAAAAAAAAAAAAAA;
    m_m_reqVec_3_rl = 66'h2AAAAAAAAAAAAAAAA;
    m_m_stateVec_0_rl = 2'h2;
    m_m_stateVec_1_rl = 2'h2;
    m_m_stateVec_2_rl = 2'h2;
    m_m_stateVec_3_rl = 2'h2;
  end
  `endif // BSV_NO_INITIAL_BLOCKS
  // synopsys translate_on
endmodule  // mkIPRqMshrWrapper


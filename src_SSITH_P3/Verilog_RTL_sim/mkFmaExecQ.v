//
// Generated by Bluespec Compiler, version 2019.05.beta2 (build a88bf40db, 2019-05-24)
//
// On Sat Jul 18 16:09:04 BST 2020
//
//
// Ports:
// Name                         I/O  size props
// RDY_enq                        O     1
// RDY_deq                        O     1
// first_data                     O    43
// RDY_first_data                 O     1
// first_poisoned                 O     1
// RDY_first_poisoned             O     1
// RDY_specUpdate_incorrectSpeculation  O     1 const
// RDY_specUpdate_correctSpeculation  O     1 const
// CLK                            I     1 clock
// RST_N                          I     1 reset
// enq_x                          I    43
// specUpdate_incorrectSpeculation_kill_all  I     1
// specUpdate_incorrectSpeculation_kill_tag  I     4
// specUpdate_correctSpeculation_mask  I    12
// EN_enq                         I     1
// EN_deq                         I     1
// EN_specUpdate_incorrectSpeculation  I     1
// EN_specUpdate_correctSpeculation  I     1
//
// No combinational paths from inputs to outputs
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

module mkFmaExecQ(CLK,
		  RST_N,

		  enq_x,
		  EN_enq,
		  RDY_enq,

		  EN_deq,
		  RDY_deq,

		  first_data,
		  RDY_first_data,

		  first_poisoned,
		  RDY_first_poisoned,

		  specUpdate_incorrectSpeculation_kill_all,
		  specUpdate_incorrectSpeculation_kill_tag,
		  EN_specUpdate_incorrectSpeculation,
		  RDY_specUpdate_incorrectSpeculation,

		  specUpdate_correctSpeculation_mask,
		  EN_specUpdate_correctSpeculation,
		  RDY_specUpdate_correctSpeculation);
  input  CLK;
  input  RST_N;

  // action method enq
  input  [42 : 0] enq_x;
  input  EN_enq;
  output RDY_enq;

  // action method deq
  input  EN_deq;
  output RDY_deq;

  // value method first_data
  output [42 : 0] first_data;
  output RDY_first_data;

  // value method first_poisoned
  output first_poisoned;
  output RDY_first_poisoned;

  // action method specUpdate_incorrectSpeculation
  input  specUpdate_incorrectSpeculation_kill_all;
  input  [3 : 0] specUpdate_incorrectSpeculation_kill_tag;
  input  EN_specUpdate_incorrectSpeculation;
  output RDY_specUpdate_incorrectSpeculation;

  // action method specUpdate_correctSpeculation
  input  [11 : 0] specUpdate_correctSpeculation_mask;
  input  EN_specUpdate_correctSpeculation;
  output RDY_specUpdate_correctSpeculation;

  // signals for module outputs
  reg RDY_deq, first_poisoned;
  wire [42 : 0] first_data;
  wire RDY_enq,
       RDY_first_data,
       RDY_first_poisoned,
       RDY_specUpdate_correctSpeculation,
       RDY_specUpdate_incorrectSpeculation;

  // inlined wires
  reg m_m_valid_for_enq_wire$wget;
  wire [11 : 0] m_m_specBits_0_lat_1$wget, m_m_specBits_1_lat_1$wget;
  wire m_m_poisoned_0_lat_0$whas,
       m_m_poisoned_1_lat_0$whas,
       m_m_poisoned_2_lat_0$whas,
       m_m_poisoned_3_lat_0$whas,
       m_m_valid_0_lat_0$whas,
       m_m_valid_0_lat_1$whas,
       m_m_valid_1_lat_0$whas,
       m_m_valid_1_lat_1$whas,
       m_m_valid_2_lat_0$whas,
       m_m_valid_2_lat_1$whas,
       m_m_valid_3_lat_0$whas,
       m_m_valid_3_lat_1$whas;

  // register m_m_deqP
  reg [1 : 0] m_m_deqP;
  wire [1 : 0] m_m_deqP$D_IN;
  wire m_m_deqP$EN;

  // register m_m_enqP
  reg [1 : 0] m_m_enqP;
  wire [1 : 0] m_m_enqP$D_IN;
  wire m_m_enqP$EN;

  // register m_m_poisoned_0_rl
  reg m_m_poisoned_0_rl;
  wire m_m_poisoned_0_rl$D_IN, m_m_poisoned_0_rl$EN;

  // register m_m_poisoned_1_rl
  reg m_m_poisoned_1_rl;
  wire m_m_poisoned_1_rl$D_IN, m_m_poisoned_1_rl$EN;

  // register m_m_poisoned_2_rl
  reg m_m_poisoned_2_rl;
  wire m_m_poisoned_2_rl$D_IN, m_m_poisoned_2_rl$EN;

  // register m_m_poisoned_3_rl
  reg m_m_poisoned_3_rl;
  wire m_m_poisoned_3_rl$D_IN, m_m_poisoned_3_rl$EN;

  // register m_m_row_0
  reg [30 : 0] m_m_row_0;
  wire [30 : 0] m_m_row_0$D_IN;
  wire m_m_row_0$EN;

  // register m_m_row_1
  reg [30 : 0] m_m_row_1;
  wire [30 : 0] m_m_row_1$D_IN;
  wire m_m_row_1$EN;

  // register m_m_row_2
  reg [30 : 0] m_m_row_2;
  wire [30 : 0] m_m_row_2$D_IN;
  wire m_m_row_2$EN;

  // register m_m_row_3
  reg [30 : 0] m_m_row_3;
  wire [30 : 0] m_m_row_3$D_IN;
  wire m_m_row_3$EN;

  // register m_m_specBits_0_rl
  reg [11 : 0] m_m_specBits_0_rl;
  wire [11 : 0] m_m_specBits_0_rl$D_IN;
  wire m_m_specBits_0_rl$EN;

  // register m_m_specBits_1_rl
  reg [11 : 0] m_m_specBits_1_rl;
  wire [11 : 0] m_m_specBits_1_rl$D_IN;
  wire m_m_specBits_1_rl$EN;

  // register m_m_specBits_2_rl
  reg [11 : 0] m_m_specBits_2_rl;
  wire [11 : 0] m_m_specBits_2_rl$D_IN;
  wire m_m_specBits_2_rl$EN;

  // register m_m_specBits_3_rl
  reg [11 : 0] m_m_specBits_3_rl;
  wire [11 : 0] m_m_specBits_3_rl$D_IN;
  wire m_m_specBits_3_rl$EN;

  // register m_m_valid_0_rl
  reg m_m_valid_0_rl;
  wire m_m_valid_0_rl$D_IN, m_m_valid_0_rl$EN;

  // register m_m_valid_1_rl
  reg m_m_valid_1_rl;
  wire m_m_valid_1_rl$D_IN, m_m_valid_1_rl$EN;

  // register m_m_valid_2_rl
  reg m_m_valid_2_rl;
  wire m_m_valid_2_rl$D_IN, m_m_valid_2_rl$EN;

  // register m_m_valid_3_rl
  reg m_m_valid_3_rl;
  wire m_m_valid_3_rl$D_IN, m_m_valid_3_rl$EN;

  // rule scheduling signals
  wire CAN_FIRE_RL_m_m_poisoned_0_canon,
       CAN_FIRE_RL_m_m_poisoned_1_canon,
       CAN_FIRE_RL_m_m_poisoned_2_canon,
       CAN_FIRE_RL_m_m_poisoned_3_canon,
       CAN_FIRE_RL_m_m_setEnqWire,
       CAN_FIRE_RL_m_m_specBits_0_canon,
       CAN_FIRE_RL_m_m_specBits_1_canon,
       CAN_FIRE_RL_m_m_specBits_2_canon,
       CAN_FIRE_RL_m_m_specBits_3_canon,
       CAN_FIRE_RL_m_m_valid_0_canon,
       CAN_FIRE_RL_m_m_valid_1_canon,
       CAN_FIRE_RL_m_m_valid_2_canon,
       CAN_FIRE_RL_m_m_valid_3_canon,
       CAN_FIRE_deq,
       CAN_FIRE_enq,
       CAN_FIRE_specUpdate_correctSpeculation,
       CAN_FIRE_specUpdate_incorrectSpeculation,
       WILL_FIRE_RL_m_m_poisoned_0_canon,
       WILL_FIRE_RL_m_m_poisoned_1_canon,
       WILL_FIRE_RL_m_m_poisoned_2_canon,
       WILL_FIRE_RL_m_m_poisoned_3_canon,
       WILL_FIRE_RL_m_m_setEnqWire,
       WILL_FIRE_RL_m_m_specBits_0_canon,
       WILL_FIRE_RL_m_m_specBits_1_canon,
       WILL_FIRE_RL_m_m_specBits_2_canon,
       WILL_FIRE_RL_m_m_specBits_3_canon,
       WILL_FIRE_RL_m_m_valid_0_canon,
       WILL_FIRE_RL_m_m_valid_1_canon,
       WILL_FIRE_RL_m_m_valid_2_canon,
       WILL_FIRE_RL_m_m_valid_3_canon,
       WILL_FIRE_deq,
       WILL_FIRE_enq,
       WILL_FIRE_specUpdate_correctSpeculation,
       WILL_FIRE_specUpdate_incorrectSpeculation;

  // remaining internal signals
  reg [11 : 0] SEL_ARR_m_m_specBits_0_rl_1_m_m_specBits_1_rl__ETC___d213;
  reg [6 : 0] SEL_ARR_m_m_row_0_11_BITS_19_TO_13_76_m_m_row__ETC___d181;
  reg [5 : 0] SEL_ARR_m_m_row_0_11_BITS_5_TO_0_03_m_m_row_1__ETC___d208;
  reg [4 : 0] SEL_ARR_m_m_row_0_11_BITS_10_TO_6_97_m_m_row_1_ETC___d202;
  reg [2 : 0] SEL_ARR_m_m_row_0_11_BITS_30_TO_28_12_m_m_row__ETC___d120;
  reg SEL_ARR_NOT_m_m_row_0_11_BIT_20_65_66_NOT_m_m__ETC___d174,
      SEL_ARR_m_m_row_0_11_BIT_11_91_m_m_row_1_13_BI_ETC___d196,
      SEL_ARR_m_m_row_0_11_BIT_12_82_m_m_row_1_13_BI_ETC___d187,
      SEL_ARR_m_m_row_0_11_BIT_21_59_m_m_row_1_13_BI_ETC___d164,
      SEL_ARR_m_m_row_0_11_BIT_22_51_m_m_row_1_13_BI_ETC___d156,
      SEL_ARR_m_m_row_0_11_BIT_23_45_m_m_row_1_13_BI_ETC___d150,
      SEL_ARR_m_m_row_0_11_BIT_24_39_m_m_row_1_13_BI_ETC___d144,
      SEL_ARR_m_m_row_0_11_BIT_25_33_m_m_row_1_13_BI_ETC___d138,
      SEL_ARR_m_m_row_0_11_BIT_26_27_m_m_row_1_13_BI_ETC___d132,
      SEL_ARR_m_m_row_0_11_BIT_27_21_m_m_row_1_13_BI_ETC___d126;
  wire [11 : 0] n__read__h8963,
		n__read__h9093,
		n__read__h9223,
		n__read__h9353,
		upd__h4230,
		upd__h4575,
		upd__h4920,
		upd__h5265;

  // action method enq
  assign RDY_enq = !m_m_valid_for_enq_wire$wget ;
  assign CAN_FIRE_enq = !m_m_valid_for_enq_wire$wget ;
  assign WILL_FIRE_enq = EN_enq ;

  // action method deq
  always@(m_m_deqP or
	  m_m_valid_0_rl or
	  m_m_valid_1_rl or m_m_valid_2_rl or m_m_valid_3_rl)
  begin
    case (m_m_deqP)
      2'd0: RDY_deq = m_m_valid_0_rl;
      2'd1: RDY_deq = m_m_valid_1_rl;
      2'd2: RDY_deq = m_m_valid_2_rl;
      2'd3: RDY_deq = m_m_valid_3_rl;
    endcase
  end
  assign CAN_FIRE_deq = RDY_deq ;
  assign WILL_FIRE_deq = EN_deq ;

  // value method first_data
  assign first_data =
	     { SEL_ARR_m_m_row_0_11_BITS_30_TO_28_12_m_m_row__ETC___d120,
	       SEL_ARR_m_m_row_0_11_BIT_27_21_m_m_row_1_13_BI_ETC___d126,
	       SEL_ARR_m_m_row_0_11_BIT_26_27_m_m_row_1_13_BI_ETC___d132,
	       SEL_ARR_m_m_row_0_11_BIT_25_33_m_m_row_1_13_BI_ETC___d138,
	       SEL_ARR_m_m_row_0_11_BIT_24_39_m_m_row_1_13_BI_ETC___d144,
	       SEL_ARR_m_m_row_0_11_BIT_23_45_m_m_row_1_13_BI_ETC___d150,
	       SEL_ARR_m_m_row_0_11_BIT_22_51_m_m_row_1_13_BI_ETC___d156,
	       SEL_ARR_m_m_row_0_11_BIT_21_59_m_m_row_1_13_BI_ETC___d164,
	       !SEL_ARR_NOT_m_m_row_0_11_BIT_20_65_66_NOT_m_m__ETC___d174,
	       SEL_ARR_m_m_row_0_11_BITS_19_TO_13_76_m_m_row__ETC___d181,
	       SEL_ARR_m_m_row_0_11_BIT_12_82_m_m_row_1_13_BI_ETC___d187,
	       SEL_ARR_m_m_row_0_11_BIT_11_91_m_m_row_1_13_BI_ETC___d196,
	       SEL_ARR_m_m_row_0_11_BITS_10_TO_6_97_m_m_row_1_ETC___d202,
	       SEL_ARR_m_m_row_0_11_BITS_5_TO_0_03_m_m_row_1__ETC___d208,
	       SEL_ARR_m_m_specBits_0_rl_1_m_m_specBits_1_rl__ETC___d213 } ;
  assign RDY_first_data = RDY_deq ;

  // value method first_poisoned
  always@(m_m_deqP or
	  m_m_poisoned_0_rl or
	  m_m_poisoned_1_rl or m_m_poisoned_2_rl or m_m_poisoned_3_rl)
  begin
    case (m_m_deqP)
      2'd0: first_poisoned = m_m_poisoned_0_rl;
      2'd1: first_poisoned = m_m_poisoned_1_rl;
      2'd2: first_poisoned = m_m_poisoned_2_rl;
      2'd3: first_poisoned = m_m_poisoned_3_rl;
    endcase
  end
  assign RDY_first_poisoned = RDY_deq ;

  // action method specUpdate_incorrectSpeculation
  assign RDY_specUpdate_incorrectSpeculation = 1'd1 ;
  assign CAN_FIRE_specUpdate_incorrectSpeculation = 1'd1 ;
  assign WILL_FIRE_specUpdate_incorrectSpeculation =
	     EN_specUpdate_incorrectSpeculation ;

  // action method specUpdate_correctSpeculation
  assign RDY_specUpdate_correctSpeculation = 1'd1 ;
  assign CAN_FIRE_specUpdate_correctSpeculation = 1'd1 ;
  assign WILL_FIRE_specUpdate_correctSpeculation =
	     EN_specUpdate_correctSpeculation ;

  // rule RL_m_m_setEnqWire
  assign CAN_FIRE_RL_m_m_setEnqWire = 1'd1 ;
  assign WILL_FIRE_RL_m_m_setEnqWire = 1'd1 ;

  // rule RL_m_m_valid_0_canon
  assign CAN_FIRE_RL_m_m_valid_0_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_valid_0_canon = 1'd1 ;

  // rule RL_m_m_valid_1_canon
  assign CAN_FIRE_RL_m_m_valid_1_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_valid_1_canon = 1'd1 ;

  // rule RL_m_m_valid_2_canon
  assign CAN_FIRE_RL_m_m_valid_2_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_valid_2_canon = 1'd1 ;

  // rule RL_m_m_valid_3_canon
  assign CAN_FIRE_RL_m_m_valid_3_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_valid_3_canon = 1'd1 ;

  // rule RL_m_m_poisoned_0_canon
  assign CAN_FIRE_RL_m_m_poisoned_0_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_poisoned_0_canon = 1'd1 ;

  // rule RL_m_m_poisoned_1_canon
  assign CAN_FIRE_RL_m_m_poisoned_1_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_poisoned_1_canon = 1'd1 ;

  // rule RL_m_m_poisoned_2_canon
  assign CAN_FIRE_RL_m_m_poisoned_2_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_poisoned_2_canon = 1'd1 ;

  // rule RL_m_m_poisoned_3_canon
  assign CAN_FIRE_RL_m_m_poisoned_3_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_poisoned_3_canon = 1'd1 ;

  // rule RL_m_m_specBits_0_canon
  assign CAN_FIRE_RL_m_m_specBits_0_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_specBits_0_canon = 1'd1 ;

  // rule RL_m_m_specBits_1_canon
  assign CAN_FIRE_RL_m_m_specBits_1_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_specBits_1_canon = 1'd1 ;

  // rule RL_m_m_specBits_2_canon
  assign CAN_FIRE_RL_m_m_specBits_2_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_specBits_2_canon = 1'd1 ;

  // rule RL_m_m_specBits_3_canon
  assign CAN_FIRE_RL_m_m_specBits_3_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_specBits_3_canon = 1'd1 ;

  // inlined wires
  assign m_m_valid_0_lat_0$whas = EN_deq && m_m_deqP == 2'd0 ;
  assign m_m_valid_0_lat_1$whas = EN_enq && m_m_enqP == 2'd0 ;
  assign m_m_valid_1_lat_0$whas = EN_deq && m_m_deqP == 2'd1 ;
  assign m_m_valid_1_lat_1$whas = EN_enq && m_m_enqP == 2'd1 ;
  assign m_m_valid_2_lat_0$whas = EN_deq && m_m_deqP == 2'd2 ;
  assign m_m_valid_2_lat_1$whas = EN_enq && m_m_enqP == 2'd2 ;
  assign m_m_valid_3_lat_0$whas = EN_deq && m_m_deqP == 2'd3 ;
  assign m_m_valid_3_lat_1$whas = EN_enq && m_m_enqP == 2'd3 ;
  assign m_m_poisoned_0_lat_0$whas =
	     EN_specUpdate_incorrectSpeculation &&
	     (specUpdate_incorrectSpeculation_kill_all ||
	      m_m_specBits_0_rl[specUpdate_incorrectSpeculation_kill_tag]) ;
  assign m_m_poisoned_1_lat_0$whas =
	     EN_specUpdate_incorrectSpeculation &&
	     (specUpdate_incorrectSpeculation_kill_all ||
	      m_m_specBits_1_rl[specUpdate_incorrectSpeculation_kill_tag]) ;
  assign m_m_poisoned_2_lat_0$whas =
	     EN_specUpdate_incorrectSpeculation &&
	     (specUpdate_incorrectSpeculation_kill_all ||
	      m_m_specBits_2_rl[specUpdate_incorrectSpeculation_kill_tag]) ;
  assign m_m_poisoned_3_lat_0$whas =
	     EN_specUpdate_incorrectSpeculation &&
	     (specUpdate_incorrectSpeculation_kill_all ||
	      m_m_specBits_3_rl[specUpdate_incorrectSpeculation_kill_tag]) ;
  assign m_m_specBits_0_lat_1$wget =
	     n__read__h8963 & specUpdate_correctSpeculation_mask ;
  assign m_m_specBits_1_lat_1$wget =
	     n__read__h9093 & specUpdate_correctSpeculation_mask ;
  always@(m_m_enqP or
	  m_m_valid_0_rl or
	  m_m_valid_1_rl or m_m_valid_2_rl or m_m_valid_3_rl)
  begin
    case (m_m_enqP)
      2'd0: m_m_valid_for_enq_wire$wget = m_m_valid_0_rl;
      2'd1: m_m_valid_for_enq_wire$wget = m_m_valid_1_rl;
      2'd2: m_m_valid_for_enq_wire$wget = m_m_valid_2_rl;
      2'd3: m_m_valid_for_enq_wire$wget = m_m_valid_3_rl;
    endcase
  end

  // register m_m_deqP
  assign m_m_deqP$D_IN = (m_m_deqP == 2'd3) ? 2'd0 : m_m_deqP + 2'd1 ;
  assign m_m_deqP$EN = EN_deq ;

  // register m_m_enqP
  assign m_m_enqP$D_IN = (m_m_enqP == 2'd3) ? 2'd0 : m_m_enqP + 2'd1 ;
  assign m_m_enqP$EN = EN_enq ;

  // register m_m_poisoned_0_rl
  assign m_m_poisoned_0_rl$D_IN =
	     !m_m_valid_0_lat_1$whas &&
	     (m_m_poisoned_0_lat_0$whas || m_m_poisoned_0_rl) ;
  assign m_m_poisoned_0_rl$EN = 1'd1 ;

  // register m_m_poisoned_1_rl
  assign m_m_poisoned_1_rl$D_IN =
	     !m_m_valid_1_lat_1$whas &&
	     (m_m_poisoned_1_lat_0$whas || m_m_poisoned_1_rl) ;
  assign m_m_poisoned_1_rl$EN = 1'd1 ;

  // register m_m_poisoned_2_rl
  assign m_m_poisoned_2_rl$D_IN =
	     !m_m_valid_2_lat_1$whas &&
	     (m_m_poisoned_2_lat_0$whas || m_m_poisoned_2_rl) ;
  assign m_m_poisoned_2_rl$EN = 1'd1 ;

  // register m_m_poisoned_3_rl
  assign m_m_poisoned_3_rl$D_IN =
	     !m_m_valid_3_lat_1$whas &&
	     (m_m_poisoned_3_lat_0$whas || m_m_poisoned_3_rl) ;
  assign m_m_poisoned_3_rl$EN = 1'd1 ;

  // register m_m_row_0
  assign m_m_row_0$D_IN = enq_x[42:12] ;
  assign m_m_row_0$EN = m_m_valid_0_lat_1$whas ;

  // register m_m_row_1
  assign m_m_row_1$D_IN = enq_x[42:12] ;
  assign m_m_row_1$EN = m_m_valid_1_lat_1$whas ;

  // register m_m_row_2
  assign m_m_row_2$D_IN = enq_x[42:12] ;
  assign m_m_row_2$EN = m_m_valid_2_lat_1$whas ;

  // register m_m_row_3
  assign m_m_row_3$D_IN = enq_x[42:12] ;
  assign m_m_row_3$EN = m_m_valid_3_lat_1$whas ;

  // register m_m_specBits_0_rl
  assign m_m_specBits_0_rl$D_IN =
	     EN_specUpdate_correctSpeculation ? upd__h4230 : n__read__h8963 ;
  assign m_m_specBits_0_rl$EN = 1'd1 ;

  // register m_m_specBits_1_rl
  assign m_m_specBits_1_rl$D_IN =
	     EN_specUpdate_correctSpeculation ? upd__h4575 : n__read__h9093 ;
  assign m_m_specBits_1_rl$EN = 1'd1 ;

  // register m_m_specBits_2_rl
  assign m_m_specBits_2_rl$D_IN =
	     EN_specUpdate_correctSpeculation ? upd__h4920 : n__read__h9223 ;
  assign m_m_specBits_2_rl$EN = 1'd1 ;

  // register m_m_specBits_3_rl
  assign m_m_specBits_3_rl$D_IN =
	     EN_specUpdate_correctSpeculation ? upd__h5265 : n__read__h9353 ;
  assign m_m_specBits_3_rl$EN = 1'd1 ;

  // register m_m_valid_0_rl
  assign m_m_valid_0_rl$D_IN =
	     m_m_valid_0_lat_1$whas ||
	     !m_m_valid_0_lat_0$whas && m_m_valid_0_rl ;
  assign m_m_valid_0_rl$EN = 1'd1 ;

  // register m_m_valid_1_rl
  assign m_m_valid_1_rl$D_IN =
	     m_m_valid_1_lat_1$whas ||
	     !m_m_valid_1_lat_0$whas && m_m_valid_1_rl ;
  assign m_m_valid_1_rl$EN = 1'd1 ;

  // register m_m_valid_2_rl
  assign m_m_valid_2_rl$D_IN =
	     m_m_valid_2_lat_1$whas ||
	     !m_m_valid_2_lat_0$whas && m_m_valid_2_rl ;
  assign m_m_valid_2_rl$EN = 1'd1 ;

  // register m_m_valid_3_rl
  assign m_m_valid_3_rl$D_IN =
	     m_m_valid_3_lat_1$whas ||
	     !m_m_valid_3_lat_0$whas && m_m_valid_3_rl ;
  assign m_m_valid_3_rl$EN = 1'd1 ;

  // remaining internal signals
  assign n__read__h8963 =
	     m_m_valid_0_lat_1$whas ? enq_x[11:0] : m_m_specBits_0_rl ;
  assign n__read__h9093 =
	     m_m_valid_1_lat_1$whas ? enq_x[11:0] : m_m_specBits_1_rl ;
  assign n__read__h9223 =
	     m_m_valid_2_lat_1$whas ? enq_x[11:0] : m_m_specBits_2_rl ;
  assign n__read__h9353 =
	     m_m_valid_3_lat_1$whas ? enq_x[11:0] : m_m_specBits_3_rl ;
  assign upd__h4230 = m_m_specBits_0_lat_1$wget ;
  assign upd__h4575 = m_m_specBits_1_lat_1$wget ;
  assign upd__h4920 = n__read__h9223 & specUpdate_correctSpeculation_mask ;
  assign upd__h5265 = n__read__h9353 & specUpdate_correctSpeculation_mask ;
  always@(m_m_deqP or m_m_row_0 or m_m_row_1 or m_m_row_2 or m_m_row_3)
  begin
    case (m_m_deqP)
      2'd0:
	  SEL_ARR_NOT_m_m_row_0_11_BIT_20_65_66_NOT_m_m__ETC___d174 =
	      !m_m_row_0[20];
      2'd1:
	  SEL_ARR_NOT_m_m_row_0_11_BIT_20_65_66_NOT_m_m__ETC___d174 =
	      !m_m_row_1[20];
      2'd2:
	  SEL_ARR_NOT_m_m_row_0_11_BIT_20_65_66_NOT_m_m__ETC___d174 =
	      !m_m_row_2[20];
      2'd3:
	  SEL_ARR_NOT_m_m_row_0_11_BIT_20_65_66_NOT_m_m__ETC___d174 =
	      !m_m_row_3[20];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1 or m_m_row_2 or m_m_row_3)
  begin
    case (m_m_deqP)
      2'd0:
	  SEL_ARR_m_m_row_0_11_BIT_24_39_m_m_row_1_13_BI_ETC___d144 =
	      m_m_row_0[24];
      2'd1:
	  SEL_ARR_m_m_row_0_11_BIT_24_39_m_m_row_1_13_BI_ETC___d144 =
	      m_m_row_1[24];
      2'd2:
	  SEL_ARR_m_m_row_0_11_BIT_24_39_m_m_row_1_13_BI_ETC___d144 =
	      m_m_row_2[24];
      2'd3:
	  SEL_ARR_m_m_row_0_11_BIT_24_39_m_m_row_1_13_BI_ETC___d144 =
	      m_m_row_3[24];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1 or m_m_row_2 or m_m_row_3)
  begin
    case (m_m_deqP)
      2'd0:
	  SEL_ARR_m_m_row_0_11_BIT_23_45_m_m_row_1_13_BI_ETC___d150 =
	      m_m_row_0[23];
      2'd1:
	  SEL_ARR_m_m_row_0_11_BIT_23_45_m_m_row_1_13_BI_ETC___d150 =
	      m_m_row_1[23];
      2'd2:
	  SEL_ARR_m_m_row_0_11_BIT_23_45_m_m_row_1_13_BI_ETC___d150 =
	      m_m_row_2[23];
      2'd3:
	  SEL_ARR_m_m_row_0_11_BIT_23_45_m_m_row_1_13_BI_ETC___d150 =
	      m_m_row_3[23];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1 or m_m_row_2 or m_m_row_3)
  begin
    case (m_m_deqP)
      2'd0:
	  SEL_ARR_m_m_row_0_11_BIT_22_51_m_m_row_1_13_BI_ETC___d156 =
	      m_m_row_0[22];
      2'd1:
	  SEL_ARR_m_m_row_0_11_BIT_22_51_m_m_row_1_13_BI_ETC___d156 =
	      m_m_row_1[22];
      2'd2:
	  SEL_ARR_m_m_row_0_11_BIT_22_51_m_m_row_1_13_BI_ETC___d156 =
	      m_m_row_2[22];
      2'd3:
	  SEL_ARR_m_m_row_0_11_BIT_22_51_m_m_row_1_13_BI_ETC___d156 =
	      m_m_row_3[22];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1 or m_m_row_2 or m_m_row_3)
  begin
    case (m_m_deqP)
      2'd0:
	  SEL_ARR_m_m_row_0_11_BIT_26_27_m_m_row_1_13_BI_ETC___d132 =
	      m_m_row_0[26];
      2'd1:
	  SEL_ARR_m_m_row_0_11_BIT_26_27_m_m_row_1_13_BI_ETC___d132 =
	      m_m_row_1[26];
      2'd2:
	  SEL_ARR_m_m_row_0_11_BIT_26_27_m_m_row_1_13_BI_ETC___d132 =
	      m_m_row_2[26];
      2'd3:
	  SEL_ARR_m_m_row_0_11_BIT_26_27_m_m_row_1_13_BI_ETC___d132 =
	      m_m_row_3[26];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1 or m_m_row_2 or m_m_row_3)
  begin
    case (m_m_deqP)
      2'd0:
	  SEL_ARR_m_m_row_0_11_BIT_25_33_m_m_row_1_13_BI_ETC___d138 =
	      m_m_row_0[25];
      2'd1:
	  SEL_ARR_m_m_row_0_11_BIT_25_33_m_m_row_1_13_BI_ETC___d138 =
	      m_m_row_1[25];
      2'd2:
	  SEL_ARR_m_m_row_0_11_BIT_25_33_m_m_row_1_13_BI_ETC___d138 =
	      m_m_row_2[25];
      2'd3:
	  SEL_ARR_m_m_row_0_11_BIT_25_33_m_m_row_1_13_BI_ETC___d138 =
	      m_m_row_3[25];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1 or m_m_row_2 or m_m_row_3)
  begin
    case (m_m_deqP)
      2'd0:
	  SEL_ARR_m_m_row_0_11_BITS_19_TO_13_76_m_m_row__ETC___d181 =
	      m_m_row_0[19:13];
      2'd1:
	  SEL_ARR_m_m_row_0_11_BITS_19_TO_13_76_m_m_row__ETC___d181 =
	      m_m_row_1[19:13];
      2'd2:
	  SEL_ARR_m_m_row_0_11_BITS_19_TO_13_76_m_m_row__ETC___d181 =
	      m_m_row_2[19:13];
      2'd3:
	  SEL_ARR_m_m_row_0_11_BITS_19_TO_13_76_m_m_row__ETC___d181 =
	      m_m_row_3[19:13];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1 or m_m_row_2 or m_m_row_3)
  begin
    case (m_m_deqP)
      2'd0:
	  SEL_ARR_m_m_row_0_11_BIT_12_82_m_m_row_1_13_BI_ETC___d187 =
	      m_m_row_0[12];
      2'd1:
	  SEL_ARR_m_m_row_0_11_BIT_12_82_m_m_row_1_13_BI_ETC___d187 =
	      m_m_row_1[12];
      2'd2:
	  SEL_ARR_m_m_row_0_11_BIT_12_82_m_m_row_1_13_BI_ETC___d187 =
	      m_m_row_2[12];
      2'd3:
	  SEL_ARR_m_m_row_0_11_BIT_12_82_m_m_row_1_13_BI_ETC___d187 =
	      m_m_row_3[12];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1 or m_m_row_2 or m_m_row_3)
  begin
    case (m_m_deqP)
      2'd0:
	  SEL_ARR_m_m_row_0_11_BIT_11_91_m_m_row_1_13_BI_ETC___d196 =
	      m_m_row_0[11];
      2'd1:
	  SEL_ARR_m_m_row_0_11_BIT_11_91_m_m_row_1_13_BI_ETC___d196 =
	      m_m_row_1[11];
      2'd2:
	  SEL_ARR_m_m_row_0_11_BIT_11_91_m_m_row_1_13_BI_ETC___d196 =
	      m_m_row_2[11];
      2'd3:
	  SEL_ARR_m_m_row_0_11_BIT_11_91_m_m_row_1_13_BI_ETC___d196 =
	      m_m_row_3[11];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1 or m_m_row_2 or m_m_row_3)
  begin
    case (m_m_deqP)
      2'd0:
	  SEL_ARR_m_m_row_0_11_BITS_10_TO_6_97_m_m_row_1_ETC___d202 =
	      m_m_row_0[10:6];
      2'd1:
	  SEL_ARR_m_m_row_0_11_BITS_10_TO_6_97_m_m_row_1_ETC___d202 =
	      m_m_row_1[10:6];
      2'd2:
	  SEL_ARR_m_m_row_0_11_BITS_10_TO_6_97_m_m_row_1_ETC___d202 =
	      m_m_row_2[10:6];
      2'd3:
	  SEL_ARR_m_m_row_0_11_BITS_10_TO_6_97_m_m_row_1_ETC___d202 =
	      m_m_row_3[10:6];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1 or m_m_row_2 or m_m_row_3)
  begin
    case (m_m_deqP)
      2'd0:
	  SEL_ARR_m_m_row_0_11_BITS_5_TO_0_03_m_m_row_1__ETC___d208 =
	      m_m_row_0[5:0];
      2'd1:
	  SEL_ARR_m_m_row_0_11_BITS_5_TO_0_03_m_m_row_1__ETC___d208 =
	      m_m_row_1[5:0];
      2'd2:
	  SEL_ARR_m_m_row_0_11_BITS_5_TO_0_03_m_m_row_1__ETC___d208 =
	      m_m_row_2[5:0];
      2'd3:
	  SEL_ARR_m_m_row_0_11_BITS_5_TO_0_03_m_m_row_1__ETC___d208 =
	      m_m_row_3[5:0];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1 or m_m_row_2 or m_m_row_3)
  begin
    case (m_m_deqP)
      2'd0:
	  SEL_ARR_m_m_row_0_11_BIT_21_59_m_m_row_1_13_BI_ETC___d164 =
	      m_m_row_0[21];
      2'd1:
	  SEL_ARR_m_m_row_0_11_BIT_21_59_m_m_row_1_13_BI_ETC___d164 =
	      m_m_row_1[21];
      2'd2:
	  SEL_ARR_m_m_row_0_11_BIT_21_59_m_m_row_1_13_BI_ETC___d164 =
	      m_m_row_2[21];
      2'd3:
	  SEL_ARR_m_m_row_0_11_BIT_21_59_m_m_row_1_13_BI_ETC___d164 =
	      m_m_row_3[21];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1 or m_m_row_2 or m_m_row_3)
  begin
    case (m_m_deqP)
      2'd0:
	  SEL_ARR_m_m_row_0_11_BIT_27_21_m_m_row_1_13_BI_ETC___d126 =
	      m_m_row_0[27];
      2'd1:
	  SEL_ARR_m_m_row_0_11_BIT_27_21_m_m_row_1_13_BI_ETC___d126 =
	      m_m_row_1[27];
      2'd2:
	  SEL_ARR_m_m_row_0_11_BIT_27_21_m_m_row_1_13_BI_ETC___d126 =
	      m_m_row_2[27];
      2'd3:
	  SEL_ARR_m_m_row_0_11_BIT_27_21_m_m_row_1_13_BI_ETC___d126 =
	      m_m_row_3[27];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1 or m_m_row_2 or m_m_row_3)
  begin
    case (m_m_deqP)
      2'd0:
	  SEL_ARR_m_m_row_0_11_BITS_30_TO_28_12_m_m_row__ETC___d120 =
	      m_m_row_0[30:28];
      2'd1:
	  SEL_ARR_m_m_row_0_11_BITS_30_TO_28_12_m_m_row__ETC___d120 =
	      m_m_row_1[30:28];
      2'd2:
	  SEL_ARR_m_m_row_0_11_BITS_30_TO_28_12_m_m_row__ETC___d120 =
	      m_m_row_2[30:28];
      2'd3:
	  SEL_ARR_m_m_row_0_11_BITS_30_TO_28_12_m_m_row__ETC___d120 =
	      m_m_row_3[30:28];
    endcase
  end
  always@(m_m_deqP or
	  m_m_specBits_0_rl or
	  m_m_specBits_1_rl or m_m_specBits_2_rl or m_m_specBits_3_rl)
  begin
    case (m_m_deqP)
      2'd0:
	  SEL_ARR_m_m_specBits_0_rl_1_m_m_specBits_1_rl__ETC___d213 =
	      m_m_specBits_0_rl;
      2'd1:
	  SEL_ARR_m_m_specBits_0_rl_1_m_m_specBits_1_rl__ETC___d213 =
	      m_m_specBits_1_rl;
      2'd2:
	  SEL_ARR_m_m_specBits_0_rl_1_m_m_specBits_1_rl__ETC___d213 =
	      m_m_specBits_2_rl;
      2'd3:
	  SEL_ARR_m_m_specBits_0_rl_1_m_m_specBits_1_rl__ETC___d213 =
	      m_m_specBits_3_rl;
    endcase
  end

  // handling of inlined registers

  always@(posedge CLK)
  begin
    if (RST_N == `BSV_RESET_VALUE)
      begin
        m_m_deqP <= `BSV_ASSIGNMENT_DELAY 2'd0;
	m_m_enqP <= `BSV_ASSIGNMENT_DELAY 2'd0;
	m_m_poisoned_0_rl <= `BSV_ASSIGNMENT_DELAY
	    1'bx /* unspecified value */ ;
	m_m_poisoned_1_rl <= `BSV_ASSIGNMENT_DELAY
	    1'bx /* unspecified value */ ;
	m_m_poisoned_2_rl <= `BSV_ASSIGNMENT_DELAY
	    1'bx /* unspecified value */ ;
	m_m_poisoned_3_rl <= `BSV_ASSIGNMENT_DELAY
	    1'bx /* unspecified value */ ;
	m_m_specBits_0_rl <= `BSV_ASSIGNMENT_DELAY
	    12'bxxxxxxxxxxxx /* unspecified value */ ;
	m_m_specBits_1_rl <= `BSV_ASSIGNMENT_DELAY
	    12'bxxxxxxxxxxxx /* unspecified value */ ;
	m_m_specBits_2_rl <= `BSV_ASSIGNMENT_DELAY
	    12'bxxxxxxxxxxxx /* unspecified value */ ;
	m_m_specBits_3_rl <= `BSV_ASSIGNMENT_DELAY
	    12'bxxxxxxxxxxxx /* unspecified value */ ;
	m_m_valid_0_rl <= `BSV_ASSIGNMENT_DELAY 1'd0;
	m_m_valid_1_rl <= `BSV_ASSIGNMENT_DELAY 1'd0;
	m_m_valid_2_rl <= `BSV_ASSIGNMENT_DELAY 1'd0;
	m_m_valid_3_rl <= `BSV_ASSIGNMENT_DELAY 1'd0;
      end
    else
      begin
        if (m_m_deqP$EN) m_m_deqP <= `BSV_ASSIGNMENT_DELAY m_m_deqP$D_IN;
	if (m_m_enqP$EN) m_m_enqP <= `BSV_ASSIGNMENT_DELAY m_m_enqP$D_IN;
	if (m_m_poisoned_0_rl$EN)
	  m_m_poisoned_0_rl <= `BSV_ASSIGNMENT_DELAY m_m_poisoned_0_rl$D_IN;
	if (m_m_poisoned_1_rl$EN)
	  m_m_poisoned_1_rl <= `BSV_ASSIGNMENT_DELAY m_m_poisoned_1_rl$D_IN;
	if (m_m_poisoned_2_rl$EN)
	  m_m_poisoned_2_rl <= `BSV_ASSIGNMENT_DELAY m_m_poisoned_2_rl$D_IN;
	if (m_m_poisoned_3_rl$EN)
	  m_m_poisoned_3_rl <= `BSV_ASSIGNMENT_DELAY m_m_poisoned_3_rl$D_IN;
	if (m_m_specBits_0_rl$EN)
	  m_m_specBits_0_rl <= `BSV_ASSIGNMENT_DELAY m_m_specBits_0_rl$D_IN;
	if (m_m_specBits_1_rl$EN)
	  m_m_specBits_1_rl <= `BSV_ASSIGNMENT_DELAY m_m_specBits_1_rl$D_IN;
	if (m_m_specBits_2_rl$EN)
	  m_m_specBits_2_rl <= `BSV_ASSIGNMENT_DELAY m_m_specBits_2_rl$D_IN;
	if (m_m_specBits_3_rl$EN)
	  m_m_specBits_3_rl <= `BSV_ASSIGNMENT_DELAY m_m_specBits_3_rl$D_IN;
	if (m_m_valid_0_rl$EN)
	  m_m_valid_0_rl <= `BSV_ASSIGNMENT_DELAY m_m_valid_0_rl$D_IN;
	if (m_m_valid_1_rl$EN)
	  m_m_valid_1_rl <= `BSV_ASSIGNMENT_DELAY m_m_valid_1_rl$D_IN;
	if (m_m_valid_2_rl$EN)
	  m_m_valid_2_rl <= `BSV_ASSIGNMENT_DELAY m_m_valid_2_rl$D_IN;
	if (m_m_valid_3_rl$EN)
	  m_m_valid_3_rl <= `BSV_ASSIGNMENT_DELAY m_m_valid_3_rl$D_IN;
      end
    if (m_m_row_0$EN) m_m_row_0 <= `BSV_ASSIGNMENT_DELAY m_m_row_0$D_IN;
    if (m_m_row_1$EN) m_m_row_1 <= `BSV_ASSIGNMENT_DELAY m_m_row_1$D_IN;
    if (m_m_row_2$EN) m_m_row_2 <= `BSV_ASSIGNMENT_DELAY m_m_row_2$D_IN;
    if (m_m_row_3$EN) m_m_row_3 <= `BSV_ASSIGNMENT_DELAY m_m_row_3$D_IN;
  end

  // synopsys translate_off
  `ifdef BSV_NO_INITIAL_BLOCKS
  `else // not BSV_NO_INITIAL_BLOCKS
  initial
  begin
    m_m_deqP = 2'h2;
    m_m_enqP = 2'h2;
    m_m_poisoned_0_rl = 1'h0;
    m_m_poisoned_1_rl = 1'h0;
    m_m_poisoned_2_rl = 1'h0;
    m_m_poisoned_3_rl = 1'h0;
    m_m_row_0 = 31'h2AAAAAAA;
    m_m_row_1 = 31'h2AAAAAAA;
    m_m_row_2 = 31'h2AAAAAAA;
    m_m_row_3 = 31'h2AAAAAAA;
    m_m_specBits_0_rl = 12'hAAA;
    m_m_specBits_1_rl = 12'hAAA;
    m_m_specBits_2_rl = 12'hAAA;
    m_m_specBits_3_rl = 12'hAAA;
    m_m_valid_0_rl = 1'h0;
    m_m_valid_1_rl = 1'h0;
    m_m_valid_2_rl = 1'h0;
    m_m_valid_3_rl = 1'h0;
  end
  `endif // BSV_NO_INITIAL_BLOCKS
  // synopsys translate_on
endmodule  // mkFmaExecQ


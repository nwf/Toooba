//
// Generated by Bluespec Compiler, version 2019.05.beta2 (build a88bf40db, 2019-05-24)
//
// On Sat Jul 18 16:22:17 BST 2020
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

module mkMinimumExecQ(CLK,
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
       m_m_valid_0_lat_0$whas,
       m_m_valid_0_lat_1$whas,
       m_m_valid_1_lat_0$whas,
       m_m_valid_1_lat_1$whas;

  // register m_m_deqP
  reg m_m_deqP;
  wire m_m_deqP$D_IN, m_m_deqP$EN;

  // register m_m_enqP
  reg m_m_enqP;
  wire m_m_enqP$D_IN, m_m_enqP$EN;

  // register m_m_poisoned_0_rl
  reg m_m_poisoned_0_rl;
  wire m_m_poisoned_0_rl$D_IN, m_m_poisoned_0_rl$EN;

  // register m_m_poisoned_1_rl
  reg m_m_poisoned_1_rl;
  wire m_m_poisoned_1_rl$D_IN, m_m_poisoned_1_rl$EN;

  // register m_m_row_0
  reg [30 : 0] m_m_row_0;
  wire [30 : 0] m_m_row_0$D_IN;
  wire m_m_row_0$EN;

  // register m_m_row_1
  reg [30 : 0] m_m_row_1;
  wire [30 : 0] m_m_row_1$D_IN;
  wire m_m_row_1$EN;

  // register m_m_specBits_0_rl
  reg [11 : 0] m_m_specBits_0_rl;
  wire [11 : 0] m_m_specBits_0_rl$D_IN;
  wire m_m_specBits_0_rl$EN;

  // register m_m_specBits_1_rl
  reg [11 : 0] m_m_specBits_1_rl;
  wire [11 : 0] m_m_specBits_1_rl$D_IN;
  wire m_m_specBits_1_rl$EN;

  // register m_m_valid_0_rl
  reg m_m_valid_0_rl;
  wire m_m_valid_0_rl$D_IN, m_m_valid_0_rl$EN;

  // register m_m_valid_1_rl
  reg m_m_valid_1_rl;
  wire m_m_valid_1_rl$D_IN, m_m_valid_1_rl$EN;

  // rule scheduling signals
  wire CAN_FIRE_RL_m_m_poisoned_0_canon,
       CAN_FIRE_RL_m_m_poisoned_1_canon,
       CAN_FIRE_RL_m_m_setEnqWire,
       CAN_FIRE_RL_m_m_specBits_0_canon,
       CAN_FIRE_RL_m_m_specBits_1_canon,
       CAN_FIRE_RL_m_m_valid_0_canon,
       CAN_FIRE_RL_m_m_valid_1_canon,
       CAN_FIRE_deq,
       CAN_FIRE_enq,
       CAN_FIRE_specUpdate_correctSpeculation,
       CAN_FIRE_specUpdate_incorrectSpeculation,
       WILL_FIRE_RL_m_m_poisoned_0_canon,
       WILL_FIRE_RL_m_m_poisoned_1_canon,
       WILL_FIRE_RL_m_m_setEnqWire,
       WILL_FIRE_RL_m_m_specBits_0_canon,
       WILL_FIRE_RL_m_m_specBits_1_canon,
       WILL_FIRE_RL_m_m_valid_0_canon,
       WILL_FIRE_RL_m_m_valid_1_canon,
       WILL_FIRE_deq,
       WILL_FIRE_enq,
       WILL_FIRE_specUpdate_correctSpeculation,
       WILL_FIRE_specUpdate_incorrectSpeculation;

  // remaining internal signals
  reg [11 : 0] CASE_m_m_deqP_0_m_m_specBits_0_rl_1_m_m_specBi_ETC__q15;
  reg [6 : 0] CASE_m_m_deqP_0_m_m_row_0_BITS_19_TO_13_1_m_m__ETC__q5;
  reg [5 : 0] CASE_m_m_deqP_0_m_m_row_0_BITS_5_TO_0_1_m_m_ro_ETC__q9;
  reg [4 : 0] CASE_m_m_deqP_0_m_m_row_0_BITS_10_TO_6_1_m_m_r_ETC__q8;
  reg [2 : 0] CASE_m_m_deqP_0_m_m_row_0_BITS_30_TO_28_1_m_m__ETC__q14;
  reg CASE_m_m_deqP_0_NOT_m_m_row_0_BIT_20_1_NOT_m_m_ETC__q4,
      CASE_m_m_deqP_0_m_m_row_0_BIT_11_1_m_m_row_1_B_ETC__q7,
      CASE_m_m_deqP_0_m_m_row_0_BIT_12_1_m_m_row_1_B_ETC__q6,
      CASE_m_m_deqP_0_m_m_row_0_BIT_21_1_m_m_row_1_B_ETC__q12,
      CASE_m_m_deqP_0_m_m_row_0_BIT_22_1_m_m_row_1_B_ETC__q3,
      CASE_m_m_deqP_0_m_m_row_0_BIT_23_1_m_m_row_1_B_ETC__q2,
      CASE_m_m_deqP_0_m_m_row_0_BIT_24_1_m_m_row_1_B_ETC__q1,
      CASE_m_m_deqP_0_m_m_row_0_BIT_25_1_m_m_row_1_B_ETC__q11,
      CASE_m_m_deqP_0_m_m_row_0_BIT_26_1_m_m_row_1_B_ETC__q10,
      CASE_m_m_deqP_0_m_m_row_0_BIT_27_1_m_m_row_1_B_ETC__q13;
  wire [27 : 0] SEL_ARR_m_m_row_0_7_BIT_27_3_m_m_row_1_9_BIT_2_ETC___d135;
  wire [21 : 0] SEL_ARR_m_m_row_0_7_BIT_21_9_m_m_row_1_9_BIT_2_ETC___d134;
  wire [11 : 0] SEL_ARR_m_m_row_0_7_BIT_11_21_m_m_row_1_9_BIT__ETC___d133,
		n__read__h5227,
		n__read__h5357,
		upd__h2528,
		upd__h2873;
  wire [8 : 0] NOT_SEL_ARR_NOT_m_m_row_0_7_BIT_20_03_04_NOT_m_ETC___d120;
  wire [4 : 0] SEL_ARR_m_m_row_0_7_BIT_26_7_m_m_row_1_9_BIT_2_ETC___d98;
  wire [2 : 0] SEL_ARR_m_m_row_0_7_BIT_24_5_m_m_row_1_9_BIT_2_ETC___d97;

  // action method enq
  assign RDY_enq = !m_m_valid_for_enq_wire$wget ;
  assign CAN_FIRE_enq = !m_m_valid_for_enq_wire$wget ;
  assign WILL_FIRE_enq = EN_enq ;

  // action method deq
  always@(m_m_deqP or m_m_valid_0_rl or m_m_valid_1_rl)
  begin
    case (m_m_deqP)
      1'd0: RDY_deq = m_m_valid_0_rl;
      1'd1: RDY_deq = m_m_valid_1_rl;
    endcase
  end
  assign CAN_FIRE_deq = RDY_deq ;
  assign WILL_FIRE_deq = EN_deq ;

  // value method first_data
  assign first_data =
	     { CASE_m_m_deqP_0_m_m_row_0_BITS_30_TO_28_1_m_m__ETC__q14,
	       SEL_ARR_m_m_row_0_7_BIT_27_3_m_m_row_1_9_BIT_2_ETC___d135,
	       CASE_m_m_deqP_0_m_m_specBits_0_rl_1_m_m_specBi_ETC__q15 } ;
  assign RDY_first_data = RDY_deq ;

  // value method first_poisoned
  always@(m_m_deqP or m_m_poisoned_0_rl or m_m_poisoned_1_rl)
  begin
    case (m_m_deqP)
      1'd0: first_poisoned = m_m_poisoned_0_rl;
      1'd1: first_poisoned = m_m_poisoned_1_rl;
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

  // rule RL_m_m_poisoned_0_canon
  assign CAN_FIRE_RL_m_m_poisoned_0_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_poisoned_0_canon = 1'd1 ;

  // rule RL_m_m_poisoned_1_canon
  assign CAN_FIRE_RL_m_m_poisoned_1_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_poisoned_1_canon = 1'd1 ;

  // rule RL_m_m_specBits_0_canon
  assign CAN_FIRE_RL_m_m_specBits_0_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_specBits_0_canon = 1'd1 ;

  // rule RL_m_m_specBits_1_canon
  assign CAN_FIRE_RL_m_m_specBits_1_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_m_specBits_1_canon = 1'd1 ;

  // inlined wires
  assign m_m_valid_0_lat_0$whas = EN_deq && m_m_deqP == 1'd0 ;
  assign m_m_valid_0_lat_1$whas = EN_enq && m_m_enqP == 1'd0 ;
  assign m_m_valid_1_lat_0$whas = EN_deq && m_m_deqP == 1'd1 ;
  assign m_m_valid_1_lat_1$whas = EN_enq && m_m_enqP == 1'd1 ;
  assign m_m_poisoned_0_lat_0$whas =
	     EN_specUpdate_incorrectSpeculation &&
	     (specUpdate_incorrectSpeculation_kill_all ||
	      m_m_specBits_0_rl[specUpdate_incorrectSpeculation_kill_tag]) ;
  assign m_m_poisoned_1_lat_0$whas =
	     EN_specUpdate_incorrectSpeculation &&
	     (specUpdate_incorrectSpeculation_kill_all ||
	      m_m_specBits_1_rl[specUpdate_incorrectSpeculation_kill_tag]) ;
  assign m_m_specBits_0_lat_1$wget =
	     n__read__h5227 & specUpdate_correctSpeculation_mask ;
  assign m_m_specBits_1_lat_1$wget =
	     n__read__h5357 & specUpdate_correctSpeculation_mask ;
  always@(m_m_enqP or m_m_valid_0_rl or m_m_valid_1_rl)
  begin
    case (m_m_enqP)
      1'd0: m_m_valid_for_enq_wire$wget = m_m_valid_0_rl;
      1'd1: m_m_valid_for_enq_wire$wget = m_m_valid_1_rl;
    endcase
  end

  // register m_m_deqP
  assign m_m_deqP$D_IN = m_m_deqP + 1'd1 ;
  assign m_m_deqP$EN = EN_deq ;

  // register m_m_enqP
  assign m_m_enqP$D_IN = m_m_enqP + 1'd1 ;
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

  // register m_m_row_0
  assign m_m_row_0$D_IN = enq_x[42:12] ;
  assign m_m_row_0$EN = m_m_valid_0_lat_1$whas ;

  // register m_m_row_1
  assign m_m_row_1$D_IN = enq_x[42:12] ;
  assign m_m_row_1$EN = m_m_valid_1_lat_1$whas ;

  // register m_m_specBits_0_rl
  assign m_m_specBits_0_rl$D_IN =
	     EN_specUpdate_correctSpeculation ? upd__h2528 : n__read__h5227 ;
  assign m_m_specBits_0_rl$EN = 1'd1 ;

  // register m_m_specBits_1_rl
  assign m_m_specBits_1_rl$D_IN =
	     EN_specUpdate_correctSpeculation ? upd__h2873 : n__read__h5357 ;
  assign m_m_specBits_1_rl$EN = 1'd1 ;

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

  // remaining internal signals
  assign NOT_SEL_ARR_NOT_m_m_row_0_7_BIT_20_03_04_NOT_m_ETC___d120 =
	     { !CASE_m_m_deqP_0_NOT_m_m_row_0_BIT_20_1_NOT_m_m_ETC__q4,
	       CASE_m_m_deqP_0_m_m_row_0_BITS_19_TO_13_1_m_m__ETC__q5,
	       CASE_m_m_deqP_0_m_m_row_0_BIT_12_1_m_m_row_1_B_ETC__q6 } ;
  assign SEL_ARR_m_m_row_0_7_BIT_11_21_m_m_row_1_9_BIT__ETC___d133 =
	     { CASE_m_m_deqP_0_m_m_row_0_BIT_11_1_m_m_row_1_B_ETC__q7,
	       CASE_m_m_deqP_0_m_m_row_0_BITS_10_TO_6_1_m_m_r_ETC__q8,
	       CASE_m_m_deqP_0_m_m_row_0_BITS_5_TO_0_1_m_m_ro_ETC__q9 } ;
  assign SEL_ARR_m_m_row_0_7_BIT_21_9_m_m_row_1_9_BIT_2_ETC___d134 =
	     { CASE_m_m_deqP_0_m_m_row_0_BIT_21_1_m_m_row_1_B_ETC__q12,
	       NOT_SEL_ARR_NOT_m_m_row_0_7_BIT_20_03_04_NOT_m_ETC___d120,
	       SEL_ARR_m_m_row_0_7_BIT_11_21_m_m_row_1_9_BIT__ETC___d133 } ;
  assign SEL_ARR_m_m_row_0_7_BIT_24_5_m_m_row_1_9_BIT_2_ETC___d97 =
	     { CASE_m_m_deqP_0_m_m_row_0_BIT_24_1_m_m_row_1_B_ETC__q1,
	       CASE_m_m_deqP_0_m_m_row_0_BIT_23_1_m_m_row_1_B_ETC__q2,
	       CASE_m_m_deqP_0_m_m_row_0_BIT_22_1_m_m_row_1_B_ETC__q3 } ;
  assign SEL_ARR_m_m_row_0_7_BIT_26_7_m_m_row_1_9_BIT_2_ETC___d98 =
	     { CASE_m_m_deqP_0_m_m_row_0_BIT_26_1_m_m_row_1_B_ETC__q10,
	       CASE_m_m_deqP_0_m_m_row_0_BIT_25_1_m_m_row_1_B_ETC__q11,
	       SEL_ARR_m_m_row_0_7_BIT_24_5_m_m_row_1_9_BIT_2_ETC___d97 } ;
  assign SEL_ARR_m_m_row_0_7_BIT_27_3_m_m_row_1_9_BIT_2_ETC___d135 =
	     { CASE_m_m_deqP_0_m_m_row_0_BIT_27_1_m_m_row_1_B_ETC__q13,
	       SEL_ARR_m_m_row_0_7_BIT_26_7_m_m_row_1_9_BIT_2_ETC___d98,
	       SEL_ARR_m_m_row_0_7_BIT_21_9_m_m_row_1_9_BIT_2_ETC___d134 } ;
  assign n__read__h5227 =
	     m_m_valid_0_lat_1$whas ? enq_x[11:0] : m_m_specBits_0_rl ;
  assign n__read__h5357 =
	     m_m_valid_1_lat_1$whas ? enq_x[11:0] : m_m_specBits_1_rl ;
  assign upd__h2528 = m_m_specBits_0_lat_1$wget ;
  assign upd__h2873 = m_m_specBits_1_lat_1$wget ;
  always@(m_m_deqP or m_m_row_0 or m_m_row_1)
  begin
    case (m_m_deqP)
      1'd0:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_24_1_m_m_row_1_B_ETC__q1 =
	      m_m_row_0[24];
      1'd1:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_24_1_m_m_row_1_B_ETC__q1 =
	      m_m_row_1[24];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1)
  begin
    case (m_m_deqP)
      1'd0:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_23_1_m_m_row_1_B_ETC__q2 =
	      m_m_row_0[23];
      1'd1:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_23_1_m_m_row_1_B_ETC__q2 =
	      m_m_row_1[23];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1)
  begin
    case (m_m_deqP)
      1'd0:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_22_1_m_m_row_1_B_ETC__q3 =
	      m_m_row_0[22];
      1'd1:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_22_1_m_m_row_1_B_ETC__q3 =
	      m_m_row_1[22];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1)
  begin
    case (m_m_deqP)
      1'd0:
	  CASE_m_m_deqP_0_NOT_m_m_row_0_BIT_20_1_NOT_m_m_ETC__q4 =
	      !m_m_row_0[20];
      1'd1:
	  CASE_m_m_deqP_0_NOT_m_m_row_0_BIT_20_1_NOT_m_m_ETC__q4 =
	      !m_m_row_1[20];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1)
  begin
    case (m_m_deqP)
      1'd0:
	  CASE_m_m_deqP_0_m_m_row_0_BITS_19_TO_13_1_m_m__ETC__q5 =
	      m_m_row_0[19:13];
      1'd1:
	  CASE_m_m_deqP_0_m_m_row_0_BITS_19_TO_13_1_m_m__ETC__q5 =
	      m_m_row_1[19:13];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1)
  begin
    case (m_m_deqP)
      1'd0:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_12_1_m_m_row_1_B_ETC__q6 =
	      m_m_row_0[12];
      1'd1:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_12_1_m_m_row_1_B_ETC__q6 =
	      m_m_row_1[12];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1)
  begin
    case (m_m_deqP)
      1'd0:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_11_1_m_m_row_1_B_ETC__q7 =
	      m_m_row_0[11];
      1'd1:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_11_1_m_m_row_1_B_ETC__q7 =
	      m_m_row_1[11];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1)
  begin
    case (m_m_deqP)
      1'd0:
	  CASE_m_m_deqP_0_m_m_row_0_BITS_10_TO_6_1_m_m_r_ETC__q8 =
	      m_m_row_0[10:6];
      1'd1:
	  CASE_m_m_deqP_0_m_m_row_0_BITS_10_TO_6_1_m_m_r_ETC__q8 =
	      m_m_row_1[10:6];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1)
  begin
    case (m_m_deqP)
      1'd0:
	  CASE_m_m_deqP_0_m_m_row_0_BITS_5_TO_0_1_m_m_ro_ETC__q9 =
	      m_m_row_0[5:0];
      1'd1:
	  CASE_m_m_deqP_0_m_m_row_0_BITS_5_TO_0_1_m_m_ro_ETC__q9 =
	      m_m_row_1[5:0];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1)
  begin
    case (m_m_deqP)
      1'd0:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_26_1_m_m_row_1_B_ETC__q10 =
	      m_m_row_0[26];
      1'd1:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_26_1_m_m_row_1_B_ETC__q10 =
	      m_m_row_1[26];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1)
  begin
    case (m_m_deqP)
      1'd0:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_25_1_m_m_row_1_B_ETC__q11 =
	      m_m_row_0[25];
      1'd1:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_25_1_m_m_row_1_B_ETC__q11 =
	      m_m_row_1[25];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1)
  begin
    case (m_m_deqP)
      1'd0:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_21_1_m_m_row_1_B_ETC__q12 =
	      m_m_row_0[21];
      1'd1:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_21_1_m_m_row_1_B_ETC__q12 =
	      m_m_row_1[21];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1)
  begin
    case (m_m_deqP)
      1'd0:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_27_1_m_m_row_1_B_ETC__q13 =
	      m_m_row_0[27];
      1'd1:
	  CASE_m_m_deqP_0_m_m_row_0_BIT_27_1_m_m_row_1_B_ETC__q13 =
	      m_m_row_1[27];
    endcase
  end
  always@(m_m_deqP or m_m_row_0 or m_m_row_1)
  begin
    case (m_m_deqP)
      1'd0:
	  CASE_m_m_deqP_0_m_m_row_0_BITS_30_TO_28_1_m_m__ETC__q14 =
	      m_m_row_0[30:28];
      1'd1:
	  CASE_m_m_deqP_0_m_m_row_0_BITS_30_TO_28_1_m_m__ETC__q14 =
	      m_m_row_1[30:28];
    endcase
  end
  always@(m_m_deqP or m_m_specBits_0_rl or m_m_specBits_1_rl)
  begin
    case (m_m_deqP)
      1'd0:
	  CASE_m_m_deqP_0_m_m_specBits_0_rl_1_m_m_specBi_ETC__q15 =
	      m_m_specBits_0_rl;
      1'd1:
	  CASE_m_m_deqP_0_m_m_specBits_0_rl_1_m_m_specBi_ETC__q15 =
	      m_m_specBits_1_rl;
    endcase
  end

  // handling of inlined registers

  always@(posedge CLK)
  begin
    if (RST_N == `BSV_RESET_VALUE)
      begin
        m_m_deqP <= `BSV_ASSIGNMENT_DELAY 1'd0;
	m_m_enqP <= `BSV_ASSIGNMENT_DELAY 1'd0;
	m_m_poisoned_0_rl <= `BSV_ASSIGNMENT_DELAY
	    1'bx /* unspecified value */ ;
	m_m_poisoned_1_rl <= `BSV_ASSIGNMENT_DELAY
	    1'bx /* unspecified value */ ;
	m_m_specBits_0_rl <= `BSV_ASSIGNMENT_DELAY
	    12'bxxxxxxxxxxxx /* unspecified value */ ;
	m_m_specBits_1_rl <= `BSV_ASSIGNMENT_DELAY
	    12'bxxxxxxxxxxxx /* unspecified value */ ;
	m_m_valid_0_rl <= `BSV_ASSIGNMENT_DELAY 1'd0;
	m_m_valid_1_rl <= `BSV_ASSIGNMENT_DELAY 1'd0;
      end
    else
      begin
        if (m_m_deqP$EN) m_m_deqP <= `BSV_ASSIGNMENT_DELAY m_m_deqP$D_IN;
	if (m_m_enqP$EN) m_m_enqP <= `BSV_ASSIGNMENT_DELAY m_m_enqP$D_IN;
	if (m_m_poisoned_0_rl$EN)
	  m_m_poisoned_0_rl <= `BSV_ASSIGNMENT_DELAY m_m_poisoned_0_rl$D_IN;
	if (m_m_poisoned_1_rl$EN)
	  m_m_poisoned_1_rl <= `BSV_ASSIGNMENT_DELAY m_m_poisoned_1_rl$D_IN;
	if (m_m_specBits_0_rl$EN)
	  m_m_specBits_0_rl <= `BSV_ASSIGNMENT_DELAY m_m_specBits_0_rl$D_IN;
	if (m_m_specBits_1_rl$EN)
	  m_m_specBits_1_rl <= `BSV_ASSIGNMENT_DELAY m_m_specBits_1_rl$D_IN;
	if (m_m_valid_0_rl$EN)
	  m_m_valid_0_rl <= `BSV_ASSIGNMENT_DELAY m_m_valid_0_rl$D_IN;
	if (m_m_valid_1_rl$EN)
	  m_m_valid_1_rl <= `BSV_ASSIGNMENT_DELAY m_m_valid_1_rl$D_IN;
      end
    if (m_m_row_0$EN) m_m_row_0 <= `BSV_ASSIGNMENT_DELAY m_m_row_0$D_IN;
    if (m_m_row_1$EN) m_m_row_1 <= `BSV_ASSIGNMENT_DELAY m_m_row_1$D_IN;
  end

  // synopsys translate_off
  `ifdef BSV_NO_INITIAL_BLOCKS
  `else // not BSV_NO_INITIAL_BLOCKS
  initial
  begin
    m_m_deqP = 1'h0;
    m_m_enqP = 1'h0;
    m_m_poisoned_0_rl = 1'h0;
    m_m_poisoned_1_rl = 1'h0;
    m_m_row_0 = 31'h2AAAAAAA;
    m_m_row_1 = 31'h2AAAAAAA;
    m_m_specBits_0_rl = 12'hAAA;
    m_m_specBits_1_rl = 12'hAAA;
    m_m_valid_0_rl = 1'h0;
    m_m_valid_1_rl = 1'h0;
  end
  `endif // BSV_NO_INITIAL_BLOCKS
  // synopsys translate_on
endmodule  // mkMinimumExecQ


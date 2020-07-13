//
// Generated by Bluespec Compiler, version 2019.05.beta2 (build a88bf40db, 2019-05-24)
//
// On Mon Jul 13 18:47:26 BST 2020
//
//
// Ports:
// Name                         I/O  size props
// RDY_enq                        O     1
// RDY_deq                        O     1
// first                          O    32
// RDY_first                      O     1
// notFull                        O     1
// RDY_notFull                    O     1 const
// notEmpty                       O     1
// RDY_notEmpty                   O     1 const
// CLK_srcClk                     I     1 clock
// RST_N_srcRst                   I     1 unused
// CLK_dstClk                     I     1 clock
// enq_sendData                   I    32
// EN_enq                         I     1
// EN_deq                         I     1
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

module mkSyncFifo_w32_d16(CLK_srcClk,
			  RST_N_srcRst,
			  CLK_dstClk,

			  enq_sendData,
			  EN_enq,
			  RDY_enq,

			  EN_deq,
			  RDY_deq,

			  first,
			  RDY_first,

			  notFull,
			  RDY_notFull,

			  notEmpty,
			  RDY_notEmpty);
  input  CLK_srcClk;
  input  RST_N_srcRst;
  input  CLK_dstClk;

  // action method enq
  input  [31 : 0] enq_sendData;
  input  EN_enq;
  output RDY_enq;

  // action method deq
  input  EN_deq;
  output RDY_deq;

  // value method first
  output [31 : 0] first;
  output RDY_first;

  // value method notFull
  output notFull;
  output RDY_notFull;

  // value method notEmpty
  output notEmpty;
  output RDY_notEmpty;

  // signals for module outputs
  wire [31 : 0] first;
  wire RDY_deq,
       RDY_enq,
       RDY_first,
       RDY_notEmpty,
       RDY_notFull,
       notEmpty,
       notFull;

  // ports of submodule q
  wire [31 : 0] q$din, q$dout;
  wire q$empty, q$full, q$rd_en, q$wr_en;

  // rule scheduling signals
  wire CAN_FIRE_deq, CAN_FIRE_enq, WILL_FIRE_deq, WILL_FIRE_enq;

  // action method enq
  assign RDY_enq = !q$full ;
  assign CAN_FIRE_enq = !q$full ;
  assign WILL_FIRE_enq = EN_enq ;

  // action method deq
  assign RDY_deq = !q$empty ;
  assign CAN_FIRE_deq = !q$empty ;
  assign WILL_FIRE_deq = EN_deq ;

  // value method first
  assign first = q$dout ;
  assign RDY_first = !q$empty ;

  // value method notFull
  assign notFull = !q$full ;
  assign RDY_notFull = 1'd1 ;

  // value method notEmpty
  assign notEmpty = !q$empty ;
  assign RDY_notEmpty = 1'd1 ;

  // submodule q
  sync_fifo_w32_d16 q(.wr_clk(CLK_srcClk),
		      .rd_clk(CLK_dstClk),
		      .din(q$din),
		      .wr_en(q$wr_en),
		      .rd_en(q$rd_en),
		      .full(q$full),
		      .empty(q$empty),
		      .dout(q$dout));

  // submodule q
  assign q$din = enq_sendData ;
  assign q$wr_en = EN_enq ;
  assign q$rd_en = EN_deq ;
endmodule  // mkSyncFifo_w32_d16


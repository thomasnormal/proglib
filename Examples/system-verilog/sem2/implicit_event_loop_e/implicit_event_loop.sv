module implicit_event_loop #(parameter integer W=4) (
    input logic [W-1:0] a,
    output logic [W-1:0] y
);
    integer i;
    always @* begin
        y = '0;
        for (i=0; i<W; i=i+1)
            if (a[i]) y = W-1-i;
    end
endmodule

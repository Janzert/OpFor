
import tango.io.Stdout;
import tango.math.random.Random;

import alphabeta;
import logging;
import position;
import goalsearch;
import staticeval;
import trapmoves;

ulong random_bit(ulong bits) {
    int num = popcount(bits);
    int bix = rand.uniformR!(int)(num);
    ulong b;
    for (int i=0; i <= bix; i++) {
        b = bits & -bits;
        bits ^= b;
    }
    return b;
}

void gen_position(inout Position pos) {
    Piece[] white_pieces;
    white_pieces = [Piece.WELEPHANT, Piece.WCAMEL, Piece.WHORSE,
        Piece.WHORSE, Piece.WDOG, Piece.WDOG, Piece.WCAT, Piece.WCAT].dup;
    Piece[] black_pieces;
    black_pieces = [Piece.BELEPHANT, Piece.BCAMEL, Piece.BHORSE,
        Piece.BHORSE, Piece.BDOG, Piece.BDOG, Piece.BCAT, Piece.BCAT].dup;

    ulong[] restricted_sqr = [0UL, RANK_8, 0, 0, 0, 0, 0,
                                   RANK_1, 0, 0, 0, 0, 0];
    int[] num_piece = [0, 8, 2, 2, 2, 1, 1,
                          8, 2, 2, 2, 1, 1];

    ulong empty = ALL_BITS_SET;
    ulong sqb;
    float[2] piece_prob;
    piece_prob[0] = rand.uniformR2!(float)(0.2, 1);
    piece_prob[1] = piece_prob[0];
    for (Piece pt=Piece.WRABBIT; pt <= Piece.BELEPHANT; pt++)
    {
        int pt_side = pt < Piece.BRABBIT ? Side.WHITE : Side.BLACK;
        for (int n=0; n < num_piece[pt]; n++)
        {
            if (pt != Piece.WELEPHANT && pt != Piece.BELEPHANT
                    && !((pt == Piece.WRABBIT || pt == Piece.BRABBIT)
                        && n == 0)) {
                if (rand.uniform!(float)() > piece_prob[pt_side])
                    continue;
            }
            sqb = random_bit(empty & ~(TRAPS
                        & ~neighbors_of(pos.placement[pt_side]))
                        & ~restricted_sqr[pt]);
            empty ^= sqb;
            pos.place_piece(pt, sqb);
        }
    }
    pos.set_steps_left(rand.uniformR2(1, 5));
}

int abs(int v) {
    return v < 0 ? -v : v;
}

int sign(int v) {
    return v < 0 ? -1 : (v > 0 ? 1 : 0);
}

int main(char[][] args) {
    Position pos = new Position();
    Position mpos = new Position();
    Logger log = new Logger();
    log.to_console = true;
    GoalSearchDT gsearch = new GoalSearchDT();
    TrapGenerator tsearch = new TrapGenerator();
    StaticEval eval = new StaticEval(log, gsearch, tsearch);
    int pos_count = 0;
    bool bad_eval = false;
    while (!bad_eval) {
        pos_count += 1;
        gen_position(pos);
        int pop = population(pos);
        int fame_score = eval.fame.score(pop);
        int eval_score = eval.static_eval(pos);
        if (eval_score < MIN_WIN_SCORE && eval_score > -MIN_WIN_SCORE) {
            Stdout.format("{}{}", pos_count, "gs"[pos.side]).newline;
            Stdout(pos.to_long_str(true)).newline;
            Stdout.format("{} steps left", pos.stepsLeft).newline;
            Stdout.format("Fame: {}", fame_score / 1.96).newline();
            Stdout.format("Eval: {}", eval_score / 1.96).newline();
            for (bitix pix=0; pix < 64; pix++) {
                Piece pt = pos.pieces[pix];
                if (pt == Piece.EMPTY)
                    continue;
                Side pside = pt < Piece.BRABBIT ? Side.WHITE : Side.BLACK;
                ulong pbit = 1UL << pix;
                int pnum = pop2count(pop, pt);
                int mpop = count2pop(pop, pt, pnum-1);
                int pval = fame_score - eval.fame.score(mpop);
                mpos.copy(pos);
                mpos.remove_piece(pix);
                ulong ntrap = neighbors_of(pbit) & TRAPS
                    & mpos.placement[pside];
                if (ntrap && !(neighbors_of(ntrap) & mpos.placement[pside])) {
                    mpos.remove_piece(bitindex(ntrap));
                }
                int peval = eval_score - eval.static_eval(mpos);
                if (sign(peval) != sign(pval)
                        && peval < MIN_WIN_SCORE
                        && peval > -MIN_WIN_SCORE) {
                    Stdout.format("{}{} F: {} E: {}, ", "xRCDHMErcdhme"[pt],
                            ix_to_alg(pix), pval, peval);
                    bad_eval = true;
                }
            }
            Stdout.newline;
        }
        pos.clear();
    }
    return 0;
}


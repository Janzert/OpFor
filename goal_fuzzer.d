
import tango.io.Stdout;
import tango.math.random.Random;

import position;
import goalsearch;

ulong random_bit(ulong bits)
{
    int num = popcount(bits);
    int bix = rand.uniformR!(int)(num);
    ulong b;
    for (int i=0; i <= bix; i++)
    {
        b = bits & -bits;
        bits ^= b;
    }
    return b;
}

void gen_possible_goal_position(inout Position pos)
{
    Piece[] white_pieces;
    white_pieces = [Piece.WELEPHANT, Piece.WCAMEL, Piece.WHORSE,
        Piece.WHORSE, Piece.WDOG, Piece.WDOG, Piece.WCAT, Piece.WCAT].dup;
    Piece[] black_pieces;
    black_pieces = [Piece.BELEPHANT, Piece.BCAMEL, Piece.BHORSE,
        Piece.BHORSE, Piece.BDOG, Piece.BDOG, Piece.BCAT, Piece.BCAT].dup;
    ulong goal_squares = RANK_8;
    ulong sqb;
    for (int i=0; i < 5; i++)
    {
        sqb = random_bit(goal_squares);
        goal_squares ^= sqb;
        pos.place_piece(Piece.BRABBIT, sqb);
    }

    ulong squares = ~RANK_8 | goal_squares;
    for (int i=0; i < white_pieces.length; i++)
    {
        sqb = random_bit(squares & ~(TRAPS
                    & ~neighbors_of(pos.placement[Side.WHITE])));
        squares ^= sqb;
        pos.place_piece(white_pieces[i], sqb);
    }
    for (int i=0; i < black_pieces.length; i++)
    {
        sqb = random_bit(squares & ~(TRAPS
                    & ~neighbors_of(pos.placement[Side.BLACK])));
        squares ^= sqb;
        pos.place_piece(black_pieces[i], sqb);
    }
    for (int i=0; i < 8; i++)
    {
        sqb = random_bit(~RANK_8 & squares & ~(TRAPS
                    & ~neighbors_of(pos.placement[Side.WHITE])));
        squares ^= sqb;
        pos.place_piece(Piece.WRABBIT, sqb);
    }
    pos.set_steps_left(4);
}

int main(char[][] args)
{
    Position pos = new Position();
    GoalSearchDT gs = new GoalSearchDT();
    int shortest_goal = gs.NOT_FOUND;
    int wgoal = shortest_goal;
    int pos_count = 0;
    while (shortest_goal == wgoal)
    {
        shortest_goal = gs.NOT_FOUND;
        StepList shortest_move;
        gs.clear_start();
        pos.clear();
        gen_possible_goal_position(pos);
        pos_count += 1;
        Stdout.format("{}w", pos_count).newline;
        Stdout(pos.to_long_str()).newline;
        PosStore moves = pos.get_moves();
        foreach(Position res; moves)
        {
            if (res.endscore() == 1)
            {
                StepList move = moves.getpos(res);
                int goal_len = 0;
                for (int i=0; i < move.numsteps; i++)
                {
                    if (move.steps[i].frombit != INV_STEP
                            && move.steps[i].tobit != INV_STEP)
                        goal_len += 1;
                }
                if (goal_len < shortest_goal)
                {
                    shortest_goal = goal_len;
                    shortest_move = move;
                }
            }
        }
        if (shortest_goal != gs.NOT_FOUND)
            shortest_move = shortest_move.dup;
        else
            shortest_move = StepList.allocate();
        moves.free_items();
        delete moves;
        if (shortest_goal < gs.NOT_FOUND)
            Stdout.format("Is white goal in {}", shortest_goal).newline;
        gs.set_start(pos);
        gs.find_goals();
        wgoal = gs.shortest[Side.WHITE];
        if (wgoal < gs.NOT_FOUND)
            Stdout.format("Goal search found white goal in {}", wgoal).newline;
        Position bpos = pos.reverse();
        gs.set_start(bpos);
        gs.find_goals();
        if (gs.shortest[Side.BLACK] != wgoal)
        {
            Stdout.format("{}b", pos_count).newline;
            Stdout.format(bpos.to_long_str()).newline;
            if (shortest_goal != gs.NOT_FOUND)
                Stdout.format("Is black goal in {}", shortest_goal).newline;
            if (gs.shortest[Side.BLACK] != gs.NOT_FOUND)
                Stdout.format("Goal search found black goal in {}",
                        gs.shortest[Side.BLACK]).newline;
            break;
        }
        Position.free(bpos);
        if (shortest_goal == gs.NOT_FOUND)
            continue;
        Position mpos = pos.dup;
        for (int i=0; i < (shortest_goal-1); i++)
        {
            mpos.do_step(shortest_move.steps[i]);
            if (mpos.inpush)
                continue;
            gs.set_start(mpos);
            gs.find_goals();
            if (gs.shortest[Side.WHITE] != (shortest_goal - (i+1)))
            {
                Stdout.format(shortest_move.to_move_str(pos)).newline;
                Stdout.format("step {}", i+1).newline;
                Stdout.format("{}w", pos_count).newline;
                Stdout(mpos.to_long_str()).newline;
                Stdout.format("Is white goal in {}", (shortest_goal - (i+1))).newline;
                Stdout.format("Search found white goal in {}",
                        gs.shortest[Side.WHITE]).newline;
                Stdout.format("\a").flush;
                return 0;
            }
            bpos = mpos.reverse();
            gs.set_start(bpos);
            gs.find_goals();
            if (gs.shortest[Side.BLACK] != (shortest_goal - (i+1)))
            {
                Stdout.format(shortest_move.to_move_str(pos)).newline;
                Stdout.format("step {}", i+1).newline;
                Stdout.format("{}w", pos_count).newline;
                Stdout(mpos.to_long_str()).newline;
                Stdout.format("Is black goal in {}",
                        (shortest_goal - (i+1))).newline;
                Stdout.format("Search found black goal in {}",
                        gs.shortest[Side.BLACK]).newline;
                Stdout.format("\a").flush;
                return 0;
            }
            Position.free(bpos);
        }
        Position.free(mpos);
        StepList.free(shortest_move);
    }

    Stdout("\a").flush;
    return 0;
}



import std.random;
import std.stdio;

import position;
import goalsearch;

ulong random_bit(ulong bits)
{
    int num = popcount(bits);
    int bix = rand() % num;
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

    /*
    int pix = rand() % white_pieces.length;
    Piece rp = white_pieces[pix];
    white_pieces[pix] = white_pieces[length-1];
    white_pieces.length = white_pieces.length - 1;
    sqb = random_bit(goal_squares);
    goal_squares ^= sqb;
    pos.place_piece(rp, sqb);

    pix = rand() % black_pieces.length;
    rp = black_pieces[pix];
    black_pieces[pix] = black_pieces[length-1];
    black_pieces.length = black_pieces.length - 1;
    sqb = random_bit(goal_squares);
    goal_squares ^= sqb;
    pos.place_piece(rp, sqb);
    */

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
    int shortest_goal = gs.wgoal;
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
        writefln("%dw", pos_count);
        writefln(pos.to_long_str());
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
            writefln("Is white goal in %d", shortest_goal);
        gs.set_start(pos);
        gs.find_goals();
        wgoal = gs.wgoal;
        if (wgoal < gs.NOT_FOUND)
            writefln("Goal search found white goal in %d", gs.wgoal);
        Position bpos = pos.reverse();
        gs.set_start(bpos);
        gs.find_goals();
        if (gs.bgoal != wgoal)
        {
            writefln("%db", pos_count);
            writefln(bpos.to_long_str());
            if (shortest_goal != gs.NOT_FOUND)
                writefln("Is black goal in %d", shortest_goal);
            if (gs.bgoal != gs.NOT_FOUND)
                writefln("Goal search found black goal in %d", gs.bgoal);
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
            if (gs.wgoal != (shortest_goal - (i+1)))
            {
                writefln(shortest_move.to_move_str(pos));
                writefln("step %d", i+1);
                writefln("%dw", pos_count);
                writefln(mpos.to_long_str());
                writefln("Is white goal in %d", (shortest_goal - (i+1)));
                writefln("Search found white goal in %d", gs.wgoal);
                writefln("\a");
                return 0;
            }
            bpos = mpos.reverse();
            gs.set_start(bpos);
            gs.find_goals();
            if (gs.bgoal != (shortest_goal - (i+1)))
            {
                writefln(shortest_move.to_move_str(pos));
                writefln("step %d", i+1);
                writefln("%dw", pos_count);
                writefln(mpos.to_long_str());
                writefln("Is black goal in %d", (shortest_goal - (i+1)));
                writefln("Search found black goal in %d", gs.bgoal);
                writefln("\a");
                return 0;
            }
            Position.free(bpos);
        }
        Position.free(mpos);
        StepList.free(shortest_move);
    }

    writefln("\a");
    return 0;
}


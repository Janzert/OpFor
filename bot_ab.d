
import std.stdio;

import aeibot;
import position;

const char[] BOT_NAME = "AB";
const char[] BOT_AUTHOR = "Janzert";

enum SType { EXACT, ALPHA, BETA }

struct TTNode
{
    ulong zobrist;
    int depth;
    int score;
    SType type;
    Step beststep;
}

class TransTable
{
    TTNode[] store;

    this (int size)
    {
        store.length = (size*1024*1024) / TTNode.sizeof;
        writefln("Initialized transposition table with %dMB and %d nodes.",
                size,
                store.length);
    }

    TTNode* get(Position pos)
    {
        int key = pos.zobrist % store.length;
        return &store[key];
    }
}

class HistoryHeuristic
{
    int[64][64][2] score;

    int get_score(Position pos, Step step)
    {
        return score[pos.side][step.fromix][step.toix];
    }

    void update(Position pos, Step step, int depth)
    {
        score[pos.side][step.fromix][step.toix] += depth;
    }

    void soften()
    {
        for (int s=0; s < 2; s++)
        {
            for (int f=0; f < 64; f++)
            {
                for (int t=0; t < 64; t++)
                {
                    score[s][f][t] /= 2;
                }
            }
        }
    }
}

class ABSearch
{
    static const int WIN_SCORE = 32000;
    static const int MAX_SCORE = 32767;
    static const int MIN_SCORE = -32767;
    static Step nullstep = { frombit: INV_STEP, tobit: INV_STEP };

    TransTable ttable;
    HistoryHeuristic cuthistory;
    Position nullmove;

    this(TransTable tt)
    {
        ttable = tt;
        cuthistory = new HistoryHeuristic();
    }

    void sortstep(Position pos, StepList steps, Step* best, int num)
    {
        if (num == 0 && best !is null && (best.frombit != 0 || best.tobit != 0))
        {
            int bix = 0;
            while (bix < steps.numsteps && steps.steps[bix] != *best)
            {
                bix++;
            }
            
            assert (bix < steps.numsteps, "Did not find best step in step list");

            if (bix < steps.numsteps)
            {
                steps.steps[bix].copy(steps.steps[0]);
                steps.steps[0].copy(*best);
            }
        }

        int score = cuthistory.get_score(pos, steps.steps[num]);
        int bix = num;
        for (int i = num+1; i < steps.numsteps; i++)
        {
            int t = cuthistory.get_score(pos, steps.steps[i]);
            if (t > score)
            {
                score = t;
                bix = i;
            }
        }

        Step tmp = steps.steps[num];
        steps.steps[num] = steps.steps[bix];
        steps.steps[bix] = tmp;
    }

    int eval(Position pos)
    {
        int score = cast(int)fastFAME(pos, 0.1716); // + (pos.zobrist % 150);
        if (pos.side == Side.BLACK)
            score = -score;
        return score;
    }

    int alphabeta(Position pos, int depth, int alpha, int beta)
    {
        int score = MIN_SCORE;
        if (pos.is_endstate())
        {
            score = pos.endscore() * WIN_SCORE;
            if (pos.side == Side.BLACK)
            {
                score = -score;
            }
            return score;
        }

        SType sflag = SType.ALPHA;
        TTNode* node = ttable.get(pos);
        Step* prev_best;
        if (node.zobrist == pos.zobrist)
        {
            if (node.depth >= depth)
            {
                if (node.type == SType.EXACT
                    || (node.type == SType.ALPHA && node.score <= alpha)
                    || (node.type == SType.BETA && node.score >= beta))
                {
                    return node.score;
                }
            }
            prev_best = &node.beststep;
        }

        if (depth < 1 && !pos.inpush)
        {
            score = eval(pos);
            if (node.zobrist != pos.zobrist)
            {
                node.beststep.clear();
            }
        } else {
            int best_ix;
            StepList steps = StepList.allocate();
            pos.get_steps(steps);
            for (int six=0; six < steps.numsteps; six++)
            {
                int cal;

                sortstep(pos, steps, prev_best, six);
                Position npos = pos.dup;
                npos.do_step(steps.steps[six]);

                if (npos == nullmove)
                {
                    cal = -(WIN_SCORE+1);   // Make this worse than a normal
                                            // loss since it's actually an illegal move
                } else if (npos.stepsLeft == 4)
                {
                    Position mynull = nullmove;
                    nullmove = npos.dup;
                    nullmove.do_step(nullstep);

                    cal = -alphabeta(npos, depth-1, -beta, -alpha);

                    Position.free(nullmove);
                    nullmove = mynull;
                } else {
                    cal = alphabeta(npos, depth-1, alpha, beta);
                }

                Position.free(npos);

                if (cal > score)
                {
                    score = cal;
                    best_ix = six;

                    if (cal > alpha)
                    {
                        alpha = cal;
                        sflag = SType.EXACT;

                        if (cal >= beta)
                        {
                            sflag = SType.BETA;
                            cuthistory.update(pos, steps.steps[best_ix], depth);
                            break;
                        }
                    }
                }
            }
            node.beststep.copy(steps.steps[best_ix]);
            StepList.free(steps);
        }

        node.zobrist = pos.zobrist;
        node.depth = depth;
        node.score = score;
        node.type = sflag;

        return score;
    }
}

class PositionNode
{
    private static PositionNode cache_head;

    PositionNode prev;
    PositionNode next;

    Position pos;
    StepList move;

    static PositionNode allocate()
    {
        if (cache_head !is null)
        {
            PositionNode n = cache_head;
            cache_head = n.next;
            n.next = null;
            return n;
        }

        return new PositionNode();
    }

    static void free(PositionNode n)
    {
        n.pos = null;
        n.prev = null;
        n.next = cache_head;
        cache_head = n.next;
    }
}

class Engine : AEIEngine
{
    ABSearch s_eng;
    PositionNode pos_list;
    PositionNode next_pos;
    int depth;
    int best_score;

    this()
    {
        s_eng = new ABSearch(new TransTable(100));
    }

    void start_search()
    {
        if (ply == 1) // white setup move
        {
            bestmove = "Ra1 Rb1 Rc1 Rd1 Re1 Rf1 Rg1 Rh1 Ha2 Db2 Cc2 Md2 Ee2 Cf2 Dg2 Hh2";
            state = EngineState.MOVESET;
        } else if (ply == 2)
        {
            if (position.pieces[11] == Piece.WELEPHANT)
            {
                bestmove = "ra8 rb8 rc8 rd8 re8 rf8 rg8 rh8 ha7 db7 cc7 ed7 me7 cf7 dg7 hh7";
            } else {
                bestmove = "ra8 rb8 rc8 rd8 re8 rf8 rg8 rh8 ha7 db7 cc7 md7 ee7 cf7 dg7 hh7";
            }
            state = EngineState.MOVESET;
        } else {
            PosStore pstore = position.get_moves();
            PositionNode last_pos;
            foreach (Position pos; pstore)
            {
                PositionNode n = PositionNode.allocate();
                n.pos = pos;
                n.move = pstore.getpos(pos);
                n.prev = last_pos;
                if (last_pos !is null)
                {
                    last_pos.next = n;
                } else {
                    pos_list = n;
                }
                last_pos = n;
            }
            delete pstore;
            next_pos = pos_list;
            best_score = ABSearch.MIN_SCORE;
            depth = 2;
            state = EngineState.SEARCHING;
        }
    }

    void search()
    {
        Position pos = next_pos.pos;
        s_eng.nullmove = pos.dup;
        s_eng.nullmove.do_step(ABSearch.nullstep);
        int score = -s_eng.alphabeta(pos, depth, ABSearch.MIN_SCORE, -best_score);
        Position.free(s_eng.nullmove);

        if (score > best_score)
        {
            best_score = score;
            
            if (next_pos !is pos_list)
            {
                PositionNode n = next_pos;
                next_pos = n.prev;

                if (n.next !is null)
                    n.next.prev = n.prev;
                n.prev.next = n.next;
                n.next = pos_list;
                n.prev = null;
                pos_list.prev = n;
                pos_list = n;
            }
        }

        if (next_pos.next !is null)
        {
            next_pos = next_pos.next;
        } else {
            depth++;
            if (depth == 5)
            {
                set_bestmove();
                state = EngineState.MOVESET;
            }
            next_pos = pos_list;
        }
    }

    void set_bestmove()
    {
        bestmove = pos_list.move.to_move_str(position);
    }

    void cleanup_search()
    {
        while (pos_list !is null)
        {
            Position.free(pos_list.pos);
            StepList.free(pos_list.move);
            PositionNode n = pos_list;
            pos_list = n.next;
            PositionNode.free(n);
        }
        s_eng.cuthistory.soften();
    }

}

int main(char[][] args)
{
    char[] ip = "127.0.0.1";
    ushort port = 40007;

    ServerInterface server = new ServerInterface(new SocketServer(ip, port),
            BOT_NAME, BOT_AUTHOR);
    writefln("Connected to server %s:%d", ip, port);
    Engine engine = new Engine();

    while (true)
    {
        if (engine.state == EngineState.IDLE)
        {
            server.check(10);
        } else {
            server.check();
        }
        while (server.current_cmd !is null)
        {
            switch (server.current_cmd.type)
            {
                case ServerCmd.CmdType.ISREADY:
                    server.readyok();
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.QUIT:
                    writefln("Exiting by server command.");
                    return 0;
                case ServerCmd.CmdType.NEWGAME:
                    if (engine.position !is null)
                    {
                        writefln(engine.position.to_long_str());
                    }
                    writefln("Starting new game.");
                    engine.new_game();
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.GO:
                    writefln("Starting search.");
                    GoCmd gcmd = cast(GoCmd)server.current_cmd;
                    engine.start_search();
                    if (gcmd.option == GoCmd.Option.INFINITE)
                    {
                        writefln("Starting infinite analyses.");
                    }
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.MAKEMOVE:
                    MoveCmd mcmd = cast(MoveCmd)server.current_cmd;
                    engine.make_move(mcmd.move);
                    writefln("made move %s\n%s", mcmd.move, engine.position.to_long_str());
                    server.clear_cmd();
                    break;
                case ServerCmd.CmdType.SETPOSITION:
                    PositionCmd pcmd = cast(PositionCmd)server.current_cmd;
                    engine.set_position(pcmd.side, pcmd.pos_str);
                    writefln("set position\n%s\n%s", 
                            "wb"[engine.position.side], 
                            engine.position.to_long_str());
                    server.clear_cmd();
                    break;
                default:
                    throw new Exception("Unhandled server command in main loop.");
            }
        }

        switch (engine.state)
        {
            case EngineState.MOVESET:
                writefln("Sending move %s", engine.bestmove);
                server.bestmove(engine.bestmove);
                engine.cleanup_search();
                writefln("Positions allocated %d, now in reserve %d.", Position.allocated, Position.reserved);
                writefln("StepLists allocated %d, now in reserve %d.", StepList.allocated, StepList.reserved);
                engine.state = EngineState.IDLE;
                break;
            case EngineState.SEARCHING:
                engine.search();
                break;
            default:
                break;
        }
    }
}


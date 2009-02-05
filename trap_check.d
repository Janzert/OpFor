
import std.stdio;

import position;
import trapmoves;

class BadCaptureException : Exception
{
    this()
    {
        super("Bad capture found");
    }
}

class TrapCheck
{
    static int UNKNOWN_VICTIMS = 1 << 14;
    enum Status { OK, LOST }

    TrapGenerator trap_gen;

    this()
    {
        trap_gen = new TrapGenerator();
    }

    int get_captures(Position pos)
    {
        int start_pop = population(pos);
        int[Piece.max+1] piece_count;
        for (Piece p=Piece.WRABBIT; p <= Piece.BELEPHANT; p++)
        {
            piece_count[p] = pop2count(start_pop, p);
        }
        PosStore moves = pos.get_moves();
        int pieceoffset = (pos.side^1) * 6;
        int victims = 0;
        foreach (Position res; moves)
        {
            int rpop = population(res);
            if (rpop != start_pop)
            {
                for (int p=Piece.WRABBIT + pieceoffset; p <= Piece.WELEPHANT + pieceoffset; p++)
                {
                    if (piece_count[p] != pop2count(rpop, cast(Piece)(p)))
                    {
                        victims |= 1 << p;
                    }
                }
            }
        }
        moves.free_items();
        delete moves;

        return victims;
    }

    Status check_captures(Position start, Position pos, StepList steps, int min_victims = UNKNOWN_VICTIMS)
    {
        int victims = get_captures(pos);
        if (min_victims != UNKNOWN_VICTIMS
                && (min_victims & ~victims))
            return Status.LOST;
        trap_gen.find_captures(pos, pos.side);
        int svictims = 0;
        for (int i=0; i < trap_gen.num_captures; i++)
        {
            if (trap_gen.captures[i].length <= pos.stepsLeft)
            {
                svictims |= 1 << trap_gen.captures[i].victim;
            }
        }
        if (victims != svictims)
        {
            for (Piece pt=Piece.WRABBIT; pt <= Piece.BELEPHANT; pt++)
            {
                if ((victims & (1 << pt)) && !(svictims & (1 << pt)))
                {
                    if (steps.numsteps)
                    {
                        writefln("Capture of %s missed after %s", "xRCDHMErcdhme"[pt],
                                steps.to_move_str(start));
                    } else {
                        writefln("Capture of %s missed by static capture", "xRCDHMErcdhme"[pt]);
                    }
                }
                else if (!(victims & (1 << pt)) && (svictims & (1 << pt)))
                {
                    if (steps.numsteps)
                    {
                        writefln("Incorrect capture of %s reported after %s",
                                "xRCDHMErcdhme"[pt], steps.to_move_str(start));
                    } else {
                        writefln("Incorrect capture of %s reported by static capture",
                                "xRCDHMErcdhme"[pt]);
                    }
                }
            }
            throw new BadCaptureException();
        }
        if (victims)
        {
            StepList legal_steps = StepList.allocate();
            pos.get_steps(legal_steps);
            CaptureInfo[] captures;
            for (int i=0; i < trap_gen.num_captures; i++)
            {
                captures ~= trap_gen.captures[i];
            }
            for (int i=0; i < captures.length; i++)
            {
                CaptureInfo cap = captures[i];
                if (pos.stepsLeft > 1 || !cap.first_step.push
                        || cap.length <= pos.stepsLeft)
                {
                    bool illegal_step = true;
                    for (int s=0; s < legal_steps.numsteps; s++)
                    {
                        if (cap.first_step == legal_steps.steps[s]
                                || (cap.first_step.push
                                    && cap.first_step.frombit == legal_steps.steps[s].frombit
                                    && cap.first_step.tobit == legal_steps.steps[s].tobit))
                        {
                            illegal_step = false;
                            break;
                        }
                    }
                    if (illegal_step)
                    {
                        if (steps.numsteps)
                        {
                            writefln("Tried to capture %s after %s with illegal step %s",
                                    "xRCDHMErcdhme"[cap.victim], steps.to_move_str(start), cap.first_step.toString(true));
                            writefln("Current pos:\n%s", pos.to_long_str());
                        } else {
                            writefln("Tried to capture %s with illegal step %s",
                                    "xRCDHMErcdhme"[cap.victim], cap.first_step.toString(true));
                        }
                        throw new BadCaptureException();
                    }
                }
                if (cap.length <= pos.stepsLeft)
                {
                    int victim = 1 << cap.victim;
                    Position npos = pos.dup;
                    npos.do_step(cap.first_step);
                    Step* nstep = steps.newstep();
                    *nstep = cap.first_step;
                    if (cap.length == 1)
                    {
                        int pop = pop2count(population(pos), cap.victim);
                        int npop = pop2count(population(npos), cap.victim);
                        if (npop != pop-1)
                        {
                            writefln("Final step didn't capture %s with %s",
                                    "xRCDHMErcdhme"[cap.victim], steps.to_move_str(start));
                            writefln("Current pos:\n%s", npos.to_long_str());
                            throw new BadCaptureException();
                        }
                    }
                    else if (!npos.inpush)
                    {
                        if (check_captures(start, npos, steps, victim) == Status.LOST)
                        {
                            writefln("Capture of %s lost after %s",
                                    "xRCDHMErcdhme"[cap.victim], steps.to_move_str(start));
                            writefln("Current pos:\n%s", npos.to_long_str());
                            throw new BadCaptureException();
                        }
                    }
                    Position.free(npos);
                    steps.pop();
                }
            }
            StepList.free(legal_steps);
        }
        return Status.OK;
    }
}


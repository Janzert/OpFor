
import tango.io.Stdout;

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
                        Stdout.format("Capture of {} missed after {}",
                                "xRCDHMErcdhme"[pt],
                                steps.to_move_str(start)).newline;
                    } else {
                        Stdout.format("Capture of {} missed by static capture",
                                "xRCDHMErcdhme"[pt]).newline;
                    }
                }
                else if (!(victims & (1 << pt)) && (svictims & (1 << pt)))
                {
                    if (steps.numsteps)
                    {
                        Stdout.format("Incorrect capture of {} reported after {}",
                                "xRCDHMErcdhme"[pt],
                                steps.to_move_str(start)).newline;
                    } else {
                        Stdout.format("Incorrect capture of {} reported by static capture",
                                "xRCDHMErcdhme"[pt]).newline;
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
                                || (cap.first_step.push && pos.stepsLeft > 1
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
                            Stdout.format("Tried to capture {} after {} with illegal step {}",
                                    "xRCDHMErcdhme"[cap.victim],
                                    steps.to_move_str(start),
                                    cap.first_step.toString(true)).newline;
                            Stdout.format("Current pos:\n{}",
                                    pos.to_long_str()).newline;
                        } else {
                            Stdout.format("Tried to capture {} with illegal step {}",
                                    "xRCDHMErcdhme"[cap.victim],
                                    cap.first_step.toString(true)).newline;
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
                    if (cap.length == 1
                            || (npos.inpush && cap.length == 2))
                    {
                        int pop = pop2count(population(pos), cap.victim);
                        int npop = pop2count(population(npos), cap.victim);
                        if (npop != pop-1)
                        {
                            Stdout.format("Final step didn't capture {} with {}",
                                    "xRCDHMErcdhme"[cap.victim],
                                    steps.to_move_str(start)).newline;
                            Stdout.format("Current pos:\n{}",
                                    npos.to_long_str()).newline;
                            throw new BadCaptureException();
                        }
                        if (npos.inpush)
                        {
                            StepList psteps = StepList.allocate();
                            npos.get_steps(psteps);
                            if (psteps.numsteps == 0)
                            {
                                Stdout.format("Could not find piece to finish capture push of {} after {}",
                                        "xRCDHMErcdhme"[cap.victim],
                                        npos.to_long_str()).newline;
                                Stdout.format("Current pos:\n{}",
                                        npos.to_long_str()).newline;
                                throw new BadCaptureException();
                            }
                            StepList.free(psteps);
                        }
                    }
                    else if (!npos.inpush)
                    {
                        if (check_captures(start, npos, steps, victim) == Status.LOST)
                        {
                            Stdout.format("Capture of {} lost after {}",
                                    "xRCDHMErcdhme"[cap.victim],
                                    steps.to_move_str(start)).newline;
                            Stdout.format("Current pos:\n{}",
                                    npos.to_long_str()).newline;
                            throw new BadCaptureException();
                        }
                    }
                    else if (cap.length > 2)
                    {
                        // is a push step
                        bool found_capture = false;
                        StepList psteps = StepList.allocate();
                        npos.get_steps(psteps);
                        for (int p=0; p < psteps.numsteps; p++)
                        {
                            Position ppos = npos.dup;
                            ppos.do_step(psteps.steps[p]);
                            (*steps.newstep()) = psteps.steps[p];
                            if (check_captures(start, ppos, steps, victim) != Status.LOST)
                                found_capture = true;
                            steps.pop();
                            Position.free(ppos);
                        }
                        StepList.free(psteps);
                        if (!found_capture)
                        {
                            Stdout.format("Capture of {} lost in push after {}",
                                    "xRCDHMErcdhme"[cap.victim],
                                    steps.to_move_str(start)).newline;
                            Stdout.format("Current pos:\n{}",
                                    npos.to_long_str()).newline;
                            throw new BadCaptureException();
                        }
                    }
                    Position.free(npos);
                    steps.pop();
                }
            }
            StepList.free(legal_steps);
        }
        trap_gen.clear();
        return Status.OK;
    }
}


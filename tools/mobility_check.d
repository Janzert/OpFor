/// Checks movement.piece_mobility, the evaluation's estimate of where each
/// piece can go, against the squares real move generation reaches.
module mobility_check;

import tango_compat;

import movement;
import position;

/// Square counts gathered by check_mobility.
struct MobilityStats
{
    uint true_moves;      /// squares pieces can really reach
    uint reported_moves;  /// squares piece_mobility found
    uint false_blockade;  /// pieces that seemed blockaded but are not
    uint true_blockade;   /// pieces that really are blockaded
    uint no_blockade;     /// pieces that are not, and were not reported so

    void add(MobilityStats other)
    {
        true_moves += other.true_moves;
        reported_moves += other.reported_moves;
        false_blockade += other.false_blockade;
        true_blockade += other.true_blockade;
        no_blockade += other.no_blockade;
    }
}

/// Throws if piece_mobility reports a square a piece cannot reach in one
/// move, or reports no squares for a piece that can move. With verbose,
/// prints how many of each piece's squares it found.
MobilityStats check_mobility(Position pos, bool verbose = false)
{
    MobilityStats stats;
    pos.set_side(Side.WHITE);
    ulong[Piece.max+1] true_movement;
    PosStore moves = pos.get_moves();
    foreach (Position result; moves)
    {
        for (int p = Piece.WRABBIT; p <= Piece.WELEPHANT; p++)
        {
            true_movement[p] |= result.bitBoards[p];
        }
    }
    moves.free_items();
    pos.set_side(Side.BLACK);
    moves = pos.get_moves();
    foreach (Position result; moves)
    {
        for (int p = Piece.BRABBIT; p <= Piece.BELEPHANT; p++)
        {
            true_movement[p] |= result.bitBoards[p];
        }
    }
    moves.free_items();
    for (int p = Piece.WRABBIT; p <= Piece.BELEPHANT; p++)
        true_movement[p] |= pos.bitBoards[p];

    ulong enemyoffset = 6;
    ulong freezers;
    ulong[Piece.max+1] reported_movement;
    for (int p = Piece.BELEPHANT; p > Piece.WRABBIT; p--)
    {
        if (p == Piece.BRABBIT)
        {
            enemyoffset = -6;
            freezers = 0UL;
            continue;
        }
        ulong pbits = pos.bitBoards[p];
        while (pbits)
        {
            ulong pbit = pbits & -pbits;
            pbits ^= pbit;
            ulong[5] move_sq;
            ulong frozen;
            piece_mobility(pos, pbit, freezers, move_sq, frozen);
            reported_movement[p] |= move_sq[4];
        }
        freezers |= pos.bitBoards[p - enemyoffset];
    }

    for (int p = Piece.WCAT; p <= Piece.max; p++)
    {
        if (p == Piece.BRABBIT)
            continue;
        if (reported_movement[p] & ~true_movement[p])
        {
            throw new Exception(Format(
                    "Moves reported for {} that could not be made:\n{}\n{}",
                    ".RCDHMErcdhme"[p],
                    bits_to_str(reported_movement[p] & ~true_movement[p]),
                    pos.to_long_str(true)));
        }
        int true_count = popcount(true_movement[p]);
        int reported_count = popcount(reported_movement[p]);
        if (verbose)
        {
            real found_per = true_count > 0
                ? (cast(real)reported_count / true_count) * 100.0
                : 100.0;
            Stdout.format("For {} found {} of {} ({:.2}) move squares.",
                    ".RCDHMErcdhme"[p],
                    reported_count, true_count, found_per).newline;
        }
        if (reported_count == 0 && true_count != 0)
        {
            throw new Exception(Format("False complete blockade for {}\n{}",
                    ".RCDHMErcdhme"[p], pos.to_long_str(true)));
        }
        stats.true_moves += true_count;
        stats.reported_moves += reported_count;
        if (reported_count < 4 && true_count >= 4)
        {
            stats.false_blockade += 1;
        }
        else if (true_count < 4)
        {
            stats.true_blockade += 1;
        } else {
            stats.no_blockade += 1;
        }
    }
    if (verbose)
    {
        real total_per = (cast(real)stats.reported_moves / stats.true_moves)
            * 100.0;
        Stdout.format("Overall for pos found {} of {} ({:.2}) move squares.",
                stats.reported_moves, stats.true_moves, total_per).newline;
    }
    return stats;
}

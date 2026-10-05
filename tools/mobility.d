/// Checks the mobility estimate on a board file, or with -r on random
/// positions until it finds an error.
import std.file : read;
import std.path : baseName;

import tango_compat;

import mobility_check;
import position;
import randompos;

int main(string[] args)
{
    if (args.length < 2)
    {
        Stdout.format("usage: {} <boardfile> | -r",
                baseName(args[0])).newline;
        return 1;
    }

    if (args[1] != "-r")
    {
        string boardstr = cast(string)read(args[1]);

        Position pos = position.parse_long_str(boardstr);
        Stdout("wb"[pos.side]).newline;
        Stdout(pos.to_long_str(true)).newline;
        Stdout(pos.to_placing_move()).newline;
        Stdout().newline;

        check_mobility(pos, true);

        return 0;
    }

    // Check randomly generated positions
    MobilityStats total;
    Position pos = new Position();
    uint pos_num;
    while (true)
    {
        pos_num++;
        random_position(pos);
        Stdout(pos_num);
        Stdout("wb"[pos.side]).newline;
        Stdout(pos.to_long_str(true)).newline;
        Stdout(pos.to_placing_move()).newline;
        total.add(check_mobility(pos, true));
        Stdout.format("All positions found {} moves of {} total ({:.2}), blockades {} false {} true {} not a blockade.",
                total.reported_moves, total.true_moves,
                (cast(real)total.reported_moves/total.true_moves) * 100.0,
                total.false_blockade, total.true_blockade,
                total.no_blockade).newline;
        Stdout.newline;
        pos.clear();
    }
}

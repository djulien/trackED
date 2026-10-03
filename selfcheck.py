"""trackED self-check with the REAL libraries (tests.py uses stand-ins).

    python selfcheck.py song.mp3 [--start 30] [--seconds 40] [--model small]
                                 [--lyrics expected.txt]

Works on a copy of an excerpt (default: 40 s from 0:30) in a temporary
folder, so nothing is written next to your song. Each step prints numbers
that should hold for any song, and things to confirm by ear:

  decode     the excerpt decodes; duration as asked
  stems      demucs: vocals + instrumental add back up to the mix (small
             error), and the vocal regions it found -- listen to the excerpt
             and check that singing starts/stops near those times
  whisper    the transcript with times; with --lyrics, the share of the
             expected words that were heard (word overlap, rough)
  mood       librosa tempo/genre/mood -- compare the tempo with the song's
             known BPM (half or double is a common, harmless miss)

Steps whose packages aren't installed are skipped (see the list at the top).
"""

import argparse
import os
import re
import shutil
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import deps  # noqa: E402


def say(ok, msg):
    print(f"  [{'PASS' if ok else 'FAIL'}] {msg}")
    return bool(ok)


def words(text):
    return re.findall(r"[a-z']+", (text or "").lower())


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("song")
    ap.add_argument("--start", type=float, default=30.0)
    ap.add_argument("--seconds", type=float, default=40.0)
    ap.add_argument("--model", default=None, help="Whisper model (default: chosen by free memory)")
    ap.add_argument("--lyrics", default=None, help="text file with the words sung in the excerpt")
    args = ap.parse_args(argv)

    print("Packages:")
    deps.main(["deps.py", "--list"])
    import timing_helpers as th
    import audio_analysis as aa
    np = th.np
    results = []

    print(f"\n== decode: {args.song}")
    total = th.get_audio_duration_seconds(args.song)
    results.append(say(total and total > 0, f"duration {th.format_time_ms(total)}"))
    if not total or np is None:
        print("Can't continue without a decodable file and numpy.")
        return 1
    start = max(0.0, min(args.start, max(0.0, total - 5)))
    seconds = min(args.seconds, total - start)
    tmp = tempfile.mkdtemp(prefix="tracked-selfcheck-")
    excerpt = os.path.join(tmp, "excerpt.wav")
    mix = aa.decode_for_demucs(args.song, 44100, 2)
    mix = mix[:, int(start * 44100):int((start + seconds) * 44100)]
    try:
        import soundfile as sf
        sf.write(excerpt, mix.T, 44100)
    except ImportError:
        print("soundfile is needed to write the excerpt; install it with the Install button.")
        return 1
    results.append(say(abs(mix.shape[1] / 44100 - seconds) < 0.1,
                       f"excerpt {th.format_time_ms(start)} + {seconds:.1f} s written to {excerpt}"))
    regions = None

    print("\n== stems (demucs)")
    if not aa.demucs_available():
        print("  skipped: demucs not installed")
    else:
        t0 = time.time()
        voc, nov, sr = aa.separate_stems(excerpt, lambda m: print("   ", m))
        print(f"  separated in {time.time() - t0:.0f} s")
        n = min(len(voc), mix.shape[1])
        ref = mix.mean(axis=0)[:n]
        err = np.sqrt(np.mean((voc[:n] + nov[:n] - ref) ** 2)) / (np.sqrt(np.mean(ref ** 2)) + 1e-9)
        results.append(say(err < 0.15, f"vocals + instrumental = mix (relative error {err:.3f}, want < 0.15)"))
        vshare = float(np.sum(voc ** 2) / (np.sum(voc ** 2) + np.sum(nov ** 2) + 1e-9))
        results.append(say(0.01 < vshare < 0.9, f"vocal energy share {vshare:.0%} (a sung song: 1%-90%)"))
        regions = aa.partition_regions(voc, nov, seconds)
        regions = aa.smooth_regions(regions, 1.0)
        print("  regions (times in the excerpt; listen to it and compare):")
        for r in regions:
            print(f"    {th.format_time_ms(r['start'])} - {th.format_time_ms(r['end'])}  {r['kind']}")
        results.append(say(any(r["kind"] in aa.VOCAL_KINDS for r in regions), "at least one vocal region found"))

    print("\n== transcription (Whisper)")
    if not aa.whisper_backends():
        print("  skipped: no Whisper backend installed")
    else:
        t0 = time.time()
        res = aa.transcribe_range(excerpt, 0.0, seconds, model_size=args.model, regions=regions,
                                  progress_cb=lambda m: print("   ", m))
        print(f"  {res.get('backend')} / {res.get('model')} in {time.time() - t0:.0f} s, source: {res.get('source')}")
        for a, b, text in res.get("segments") or []:
            print(f"    {th.format_time_ms(a)} - {th.format_time_ms(b)}  {text}")
        results.append(say(bool(words(res.get("text"))), "some words were transcribed"))
        if args.lyrics:
            want = words(open(args.lyrics, encoding="utf-8").read())
            got = set(words(res.get("text")))
            hit = sum(1 for w in want if w in got) / max(1, len(want))
            results.append(say(hit >= 0.5, f"{hit:.0%} of the expected words were heard (want >= 50%)"))

    print("\n== genre / mood (librosa)")
    if not aa.genre_mood_available():
        print("  skipped: librosa not installed")
    else:
        gm = aa.estimate_genre_mood(excerpt)
        print(f"  tempo {gm['tempo']} BPM, genre {gm['genre']} ({gm['confidence']}), mood {gm['mood']}")
        results.append(say(40 <= gm["tempo"] <= 220, "tempo in a plausible range (compare with the known BPM)"))

    shutil.rmtree(tmp, ignore_errors=True)
    print(f"\n{sum(results)} of {len(results)} checks passed.")
    return 0 if all(results) else 1


if __name__ == "__main__":
    sys.exit(main())

// chanlun-v1 C# backend: core typed records.
//
// Mirrors impl/go/internal/chanlun and conformance/chanlun-v1/reference_backend
// type shapes. All numeric fields are `long` (the chanlun-v1 corpus is
// integer-core; no floats anywhere).

namespace Chanlun;

/// <summary>Price interval bar {l, h}.</summary>
public readonly record struct Bar(long L, long H);

/// <summary>Def-3 fractal {idx, kind, h, l}, kind in {"top","bottom"}.</summary>
public readonly record struct Fractal(long Idx, string Kind, long H, long L);

/// <summary>Def-4 stroke {from_idx, to_idx, dir, from_p, to_p}.</summary>
public readonly record struct Stroke(long FromIdx, long ToIdx, string Dir, long FromP, long ToP);

/// <summary>Stroke element {idx, lo, hi} for level-N+1 zhongshu input.</summary>
public readonly record struct Element(long Idx, long Lo, long Hi);

/// <summary>Zhongshu center {start, end, ZD, ZG, n}.</summary>
public readonly record struct Center(long Start, long End, long ZD, long ZG, long N);

/// <summary>Named string constants used across the pipeline.</summary>
public static class Kinds
{
    public const string Top = "top";
    public const string Bottom = "bottom";
}

public static class Dispositions
{
    public const string First = "first";
    public const string Absorbed = "absorbed";
    public const string Emit = "emit";
    public const string Residue = "residue";
}

public static class TrendTypes
{
    public const string Consolidation = "consolidation";
    public const string Up = "trend_up";
    public const string Down = "trend_down";
    public const string Mixed = "mixed";
    public const string None = "none";
}

/// <summary>Pipeline result shape matching reference_backend.pipeline.run_full.</summary>
public sealed record PipelineResult(
    IReadOnlyList<Bar> NormalizedBars,
    IReadOnlyList<Fractal> Fractals,
    IReadOnlyList<string> StrokeDispositions,
    IReadOnlyList<Stroke> Strokes,
    IReadOnlyList<Element> StrokeElements,
    string ZhongshuZone,
    IReadOnlyList<Center> ZhongshuCenters,
    string TrendType);

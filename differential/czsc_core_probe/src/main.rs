use std::{env, fs, path::Path, sync::Arc};

use chrono::{Duration, TimeZone, Utc};
use czsc_core::analyze::CZSC;
use czsc_core::objects::{bar::RawBar, direction::Direction, freq::Freq, mark::Mark};
use serde::Deserialize;
use serde_json::{Value, json};

#[derive(Deserialize)]
struct Manifest {
    entries: Vec<Entry>,
}

#[derive(Deserialize)]
struct Entry {
    id: String,
    stage: String,
    file: String,
}

fn intish(v: f64) -> Value {
    if v.fract() == 0.0 {
        json!(v as i64)
    } else {
        json!(v)
    }
}

fn bars_to_raw(bars: &[Value]) -> Vec<RawBar> {
    let start = Utc.with_ymd_and_hms(2020, 1, 1, 0, 0, 0).unwrap();
    bars.iter()
        .enumerate()
        .map(|(i, b)| {
            let h = b["h"].as_f64().unwrap();
            let l = b["l"].as_f64().unwrap();
            let mid = (h + l) / 2.0;
            RawBar {
                symbol: Arc::from("CHANLUN"),
                dt: start + Duration::days(i as i64),
                freq: Freq::D,
                id: i as i32,
                open: mid,
                close: mid,
                high: h,
                low: l,
                vol: 1.0,
                amount: 1.0,
            }
        })
        .collect()
}

fn project(input: &Value) -> Value {
    let bars_v = input["bars"].as_array().unwrap();
    if bars_v.is_empty() {
        return json!({
            "normalized_bars": [],
            "fractals": [],
            "strokes": [],
            "zhongshu_centers": []
        });
    }

    let c = CZSC::new(bars_to_raw(bars_v), 200);
    let normalized: Vec<Value> = c
        .bars_ubi
        .iter()
        .map(|b| json!({"h": intish(b.high), "l": intish(b.low)}))
        .collect();
    let fractals: Vec<Value> = c
        .get_fx_list()
        .iter()
        .map(|f| {
            let raw = &f.elements[f.elements.len() / 2];
            json!({
                "idx": raw.id,
                "kind": match f.mark { Mark::G => "top", Mark::D => "bottom" },
                "h": intish(f.high),
                "l": intish(f.low),
            })
        })
        .collect();
    let strokes: Vec<Value> = c
        .bi_list
        .iter()
        .map(|bi| {
            let a = &bi.fx_a.elements[bi.fx_a.elements.len() / 2];
            let b = &bi.fx_b.elements[bi.fx_b.elements.len() / 2];
            json!({
                "from_idx": a.id,
                "to_idx": b.id,
                "dir": match bi.direction { Direction::Up => "up", Direction::Down => "down" },
                "from_p": intish(bi.fx_a.fx),
                "to_p": intish(bi.fx_b.fx),
            })
        })
        .collect();

    json!({
        "normalized_bars": normalized,
        "fractals": fractals,
        "strokes": strokes,
        "zhongshu_centers": []
    })
}

fn main() {
    let corpus = env::args()
        .nth(1)
        .expect("usage: czsc-core-probe <corpus-dir>");
    let manifest_path = Path::new(&corpus).join("manifest.json");
    let manifest: Manifest =
        serde_json::from_str(&fs::read_to_string(manifest_path).unwrap()).unwrap();
    let mut out = serde_json::Map::new();
    for entry in manifest.entries {
        if entry.stage != "pipeline" {
            continue;
        }
        let fixture: Value =
            serde_json::from_str(&fs::read_to_string(Path::new(&corpus).join(entry.file)).unwrap())
                .unwrap();
        out.insert(entry.id, project(&fixture["input"]));
    }
    println!("{}", Value::Object(out));
}

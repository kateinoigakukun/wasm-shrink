use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    fs::File,
    path::PathBuf,
    process::{Command, Stdio},
};
use structopt::StructOpt;
use tempfile::tempdir;

#[derive(StructOpt, Debug)]
enum Opt {
    Init {
        /// git repository
        #[structopt(name = "REPO")]
        repo: String,

        /// working directory
        #[structopt(short, long)]
        workdir: Option<PathBuf>,

        /// target .wasm file
        #[structopt(short, long)]
        target: PathBuf,

        /// output data file
        #[structopt(short, long)]
        output: PathBuf,
    },

    Update {
        /// git repository
        #[structopt(name = "REPO")]
        repo: String,

        /// working directory
        #[structopt(short, long)]
        workdir: Option<PathBuf>,

        /// JSON file to update
        #[structopt(short, long)]
        data: PathBuf,
    },
}

impl Opt {
    fn repo(&self) -> &str {
        match self {
            Opt::Init { repo, .. } => repo,
            Opt::Update { repo, .. } => repo,
        }
    }

    fn workdir(&self) -> &Option<PathBuf> {
        match self {
            Opt::Init { workdir, .. } => workdir,
            Opt::Update { workdir, .. } => workdir,
        }
    }
}

#[derive(Serialize, Deserialize)]
struct Record {
    rev: String,
    date: DateTime<Utc>,
    sizes: HashMap<String, u64>,
    rates: HashMap<String, f64>,
}
#[derive(Serialize, Deserialize)]
struct TargetBenchmark {
    name: String,
    records: Vec<Record>,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let opt = Opt::from_args();

    let mut tempdir_owner = None;

    let workdir = if let Some(workdir) = opt.workdir() {
        workdir.clone()
    } else {
        let tempdir = tempdir()?;
        let path = tempdir.path().clone().to_path_buf();
        tempdir_owner = Some(tempdir);
        path
    };

    // Clone repo in work dir
    log::debug!("Cloning repo into {:?}", workdir);
    exec(
        Command::new("git")
            .arg("clone")
            .arg(opt.repo())
            .arg(&workdir),
    )?;

    let result = match &opt {
        Opt::Init { target, .. } => {
            let revs = revs_since(None, &workdir)?;
            let records = collect_records(revs, &workdir, &target)?;
            TargetBenchmark {
                name: target.to_string_lossy().to_string(),
                records,
            }
        }
        Opt::Update { data, .. } => {
            let data = File::open(data)?;
            let mut data: TargetBenchmark = serde_json::from_reader(data)?;
            let latest_rev = data.records.first().map(|r| r.rev.as_str());
            let revs = revs_since(latest_rev, &workdir)?;
            let target = PathBuf::from(&data.name);
            let mut records = collect_records(revs, &workdir, &target)?;
            records.append(&mut data.records);

            TargetBenchmark {
                name: data.name,
                records,
            }
        }
    };

    let output = match opt {
        Opt::Init { output, .. } => output,
        Opt::Update { data, .. } => data,
    };
    let output = File::create(output)?;
    serde_json::to_writer_pretty(output, &result)?;

    let _ = tempdir_owner;
    Ok(())
}

fn exec(cmd: &mut Command) -> Result<String, Box<dyn std::error::Error>> {
    log::debug!("{:?}", cmd);
    let output = cmd.stderr(Stdio::inherit()).output()?;
    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).into_owned())
    } else {
        Err(format!("{:?}", output).into())
    }
}

fn measure_size_in_rev(
    rev: &str,
    workdir: &PathBuf,
    target_exe: &PathBuf,
    strategies: &[&str],
) -> Result<HashMap<String, u64>, Box<dyn std::error::Error>> {
    exec(
        Command::new("git")
            .arg("checkout")
            .arg(rev)
            .current_dir(workdir),
    )?;

    let sizes = strategies
        .iter()
        .filter_map(|strategy| {
            let size = run_and_measure(workdir, target_exe, strategy).ok()?;
            Some((String::from(*strategy), size))
        })
        .collect::<HashMap<_, _>>();

    Ok(sizes)
}

fn run_and_measure(
    workdir: &PathBuf,
    target_exe: &PathBuf,
    strategy: &str,
) -> Result<u64, Box<dyn std::error::Error>> {
    let temp_output = tempfile::NamedTempFile::new()?;
    exec(
        Command::new("cargo")
            .arg("run")
            .arg("--release")
            .arg(target_exe)
            .arg("--output")
            .arg(temp_output.path())
            .arg("--merge-strategy")
            .arg(strategy)
            .current_dir(workdir),
    )?;

    let size = std::fs::metadata(temp_output.path())?.len();
    if size == 0 {
        return Err("no output".into());
    }
    Ok(size)
}

fn collect_records(
    revs: Vec<String>,
    workdir: &PathBuf,
    target: &PathBuf,
) -> Result<Vec<Record>, Box<dyn std::error::Error>> {
    let mut records = Vec::new();
    let abs_target = target.canonicalize()?;
    let original_size = std::fs::metadata(&abs_target)?.len();

    let strategies_info = [
        // (stategy id, since rev)

        // commit 8f2c0f562d3e06e6d06497974e908315bba92d8a
        // Author: Yuta Saito <kateinoigakukun@gmail.com>
        // Date:   Tue Oct 12 17:17:55 2021 +0900
        //
        //     code: use absolute path to run the shrinker
        //
        ("exact-match", "8f2c0f562d3e06e6d06497974e908315bba92d8a"),

        // commit c8bbd6a4050d3480d0c693f5da58e8d5260fda9a
        // Author: Yuta Saito <kateinoigakukun@gmail.com>
        // Date:   Sun Oct 24 10:03:29 2021 +0900
        //
        //     chore: ignore .trace profiler artifacts for Instruments.app
        //
        ("const-param", "c8bbd6a4050d3480d0c693f5da58e8d5260fda9a"),
    ];

    let mut strategies = vec![];

    for rev in revs.iter().rev() {
        let mut new_strategies = strategies_info.iter().filter_map(|(id, since_rev)| {
            if *since_rev == rev {
                Some(*id)
            } else {
                None
            }
        }).collect::<Vec<_>>();
        if !new_strategies.is_empty() {
            strategies.append(&mut new_strategies);
        }
        let date = exec(
            Command::new("git")
                .arg("show")
                .arg("-s")
                .arg("--format=%cD")
                .arg(&rev)
                .current_dir(&workdir),
        )?;
        println!("{}", date);
        let date = DateTime::parse_from_rfc2822(&date.trim_end())?.with_timezone(&Utc);
        let record = match measure_size_in_rev(&rev, &workdir, &abs_target, &strategies) {
            Ok(sizes) => {
                let rates = sizes
                    .iter()
                    .map(|(key, size)| (key.clone(), *size as f64 / original_size as f64))
                    .collect();
                log::info!("{} {:?}", rev, sizes);
                Record {
                    rev: rev.to_string(),
                    date,
                    sizes,
                    rates,
                }
            }
            Err(err) => {
                log::warn!("failed to measure size in {}: {}", rev, err);
                Record {
                    rev: rev.to_string(),
                    date,
                    sizes: HashMap::new(),
                    rates: HashMap::new(),
                }
            }
        };
        records.push(record);
    }
    Ok(records)
}

fn revs_since(
    rev: Option<&str>,
    workdir: &PathBuf,
) -> Result<Vec<String>, Box<dyn std::error::Error>> {
    let mut cmd = Command::new("git");
    let mut cmd = cmd.arg("rev-list");

    if let Some(since_rev) = rev {
        cmd = cmd.arg(format!("{}..HEAD", since_rev));
    } else {
        cmd = cmd.arg("HEAD");
    }

    let revs = exec(cmd.current_dir(&workdir))?;
    if revs.is_empty() {
        return Ok(Vec::new());
    }
    let revs = revs
        .trim_end()
        .split("\n")
        .map(String::from)
        .collect::<Vec<_>>();
    Ok(revs)
}

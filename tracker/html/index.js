function humanReadableFileSize(bytes) {
    const units = ['B', 'kB', 'MB', 'GB', 'TB', 'PB', 'EB', 'ZB', 'YB'];
    let unitIndex = 0;

    while (Math.round(bytes) >= 1024 && unitIndex < units.length) {
        bytes /= 1024;
        ++unitIndex;
    }

    return (Math.round(bytes * 100) / 100) + ' ' + units[unitIndex];
}

async function start() {
    const response = await fetch('./data/swift-hello.wasm.json');
    const json = await response.json();

    const records = json.records.reverse();
    const categories = records.map(record => record.date);
    const strategies = ["exact-match", "const-param"];
    const series = strategies.map(strategy => {
        let data = records.map(record => {
            return { y: record.sizes[strategy], rate: record.rates[strategy], rev: record.rev, date: record.date }
        });
        return { name: strategy, data }
    });

    Highcharts.chart('container', {
        title: {
            text: json.name
        },

        xAxis: {
            categories
        },
        yAxis: {
            title: {
                text: "File Size"
            },
            labels: {
                formatter: function () {
                    return humanReadableFileSize(this.value);
                }
            }
        },
        tooltip: {
            formatter: function () {
                const commitLink = "https://github.com/kateinoigakukun/wasm-shrink/commit/" + this.point.rev
                return `size: ${this.y}<br>rate: ${this.point.rate}<br>date: ${this.point.date}<br>rev: <a href=${commitLink} target="_blank" > ${this.point.rev}</a>`;
            },
            style: {
                pointerEvents: 'auto',
            }
        },
        series
    });
}

document.addEventListener('DOMContentLoaded', start);
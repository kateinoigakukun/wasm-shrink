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
    const response = await fetch('./data.json');
    const json = await response.json();

    const records = json.records.reverse();
    const categories = records.map(record => record.date);
    const data = records.map(record => {
        return { y: record.size, rev: record.rev, date: record.date }
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
            formatter: function() {
                return `size: ${this.y}<br>rate: ${this.point.rate}<br>date: ${this.point.date}<br>rev: ${this.point.rev}`;
            }
        },
        series: [{ name: json.name, data }]
    });
}

document.addEventListener('DOMContentLoaded', start);
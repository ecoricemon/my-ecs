// Initialize wasm.
import * as wasm from './pkg/wasm-index.js';
await wasm.default();

const btn = document.getElementById('btnCpu');
const text = btn.innerHTML.replace('N', wasm.numCpus());
btn.innerHTML = text;

// === Buttons ===

const drawBtns = ['btnCpu', 'btnSingleWorker'];

drawBtns.forEach((id) => document.getElementById(id).addEventListener('click', () => draw(id)));
document.getElementById('btnStop').addEventListener('click', stop);

function enableDrawButtons() {
  drawBtns.forEach((id) => {
    const btn = document.getElementById(id);
    btn.disabled = false;
    btn.style.color = 'white';
  });
  document.getElementById('btnStop').disabled = true;
}

function disableDrawButtons(id) {
  drawBtns.forEach((id) => document.getElementById(id).disabled = true);
  document.getElementById(id).style.color = '#2069FA';
  document.getElementById('btnStop').disabled = false;
}

enableDrawButtons();

// === Canvas ===

// We're going to draw fractal images onto this fixed size canvas not to
// bring difference caused by real canvas size.
const baseCanvas = document.createElement('canvas');
baseCanvas.width = wasm.canvasWidth();
baseCanvas.height = wasm.canvasHeight();
const baseCx = baseCanvas.getContext('2d');

// This is real canvas we will see on the screen.
const canvas = document.getElementById('canvas');
const cx = canvas.getContext('2d');

// Wasm will fill this buffer with a fractal image.
const buf = new Uint8ClampedArray(baseCanvas.width * baseCanvas.height * 4);
const imageData = new ImageData(buf, baseCanvas.width, baseCanvas.height);

// === Target area ===

// Fractal images will be drawn in complex plane. (width, height) and (x, y)
// are an area and its center in complex plane respectively.
let width = 0;
let height = 0;
let x = 0;
let y = 0;
let lastZoomAt = 0;

function resetTargetArea() {
  width = 10.0;
  height = 10.0;
  x = -0.743643887037151
  y = 0.13182590420533
  lastZoomAt = performance.now();
}

function zoomInTargetArea() {
  const now = performance.now();
  const elapsedMs = now - lastZoomAt;
  lastZoomAt = now;

  const zoomRatio = getZoomRatio(elapsedMs);
  width *= zoomRatio;
  height *= zoomRatio;
}

function getZoomRatio(elapsedMs) {
  // Keep the old feel as the reference: zoomRatio 0.99 for a frame every 16.67ms.
  const referenceFrameMs = 1000 / 60;
  const referenceZoomRatio = 0.99;
  return Math.pow(referenceZoomRatio, elapsedMs / referenceFrameMs);
}

// === Measurement ===

let start = undefined;
let frames = 0;
let timer = undefined;

function resetMeasure() {
  start = performance.now();
  frames = 0;
  timer = setInterval(() => {
    const elapsed = performance.now() - start;
    const x = (frames / elapsed) * 1000;
    const fps = Math.round(x * 10) / 10;
    document.getElementById('fps').innerHTML = `${fps} fps`;
  }, 1000);
}

function stopMeasure() {
  if (timer !== undefined) {
    clearInterval(timer);
  }
}

// === Execution ===

let app = undefined;
let run = false;
let age = 0;

function draw(id) {
  if (!run) {
    resetTargetArea();
    disableDrawButtons(id);
    resetMeasure();
    age = wasm.startAge();
    run = true;
    createApp(id);
    requestCalculation();
  }
}

function stop() {
  if (run) {
    stopMeasure();
    enableDrawButtons();
    app.destroy();
    run = false;
  }
}

function createApp(ty) {
  app = new wasm.App(ty);

  app.setOnMessage(() => {
    drawImage();
    frames += 1;

    if (run && width > 0.0001) {
      zoomInTargetArea();
      requestCalculation();
    } else {
      stop();
    }
  });
}

// Function to request fractal image calculation to wasm.
function requestCalculation() {
  app.calcImageOnCpu(
    age,
    x - width / 2,
    x + width / 2,
    y - height / 2,
    y + height / 2
  );
  age += 1;
}

// Draws an image from wasm data with scaling.
function drawImage() {
  if (app.getResult(buf) !== 'ready') {
    return;
  }
  draw();

  function draw() {
    baseCx.putImageData(imageData, 0, 0);
    canvas.width = canvas.clientWidth; // this clears canvas
    canvas.height = canvas.clientHeight;
    cx.drawImage(
      baseCanvas,
      0,
      0,
      baseCanvas.width,
      baseCanvas.height,
      0,
      0,
      canvas.width,
      canvas.height
    );
  }
}

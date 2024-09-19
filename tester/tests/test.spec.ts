import { test, expect } from '@playwright/test';

test('web test', async ({ page }) => {
  let errors: Array<Error> = [];
  page.on('pageerror', error => {
    errors.push(error);
  });

  let err_msgs: Array<string> = [];
  page.on('console', msg => {
    if (msg.type() === 'error')
      err_msgs.push(msg.text());
    else
      console.log(msg.text());
  });

  page.on('worker', worker => {
    const now = nowString();
    const url = worker.url();
    console.log(`${now} [I] worker created: ${url}`);

    worker.on('close', worker => {
      const now = nowString();
      const url = worker.url();
      console.log(`${now} [I] worker destroyed: ${url}`);
    });
  });

  await page.goto('./');

  await page.waitForEvent('console', {
    predicate: msg => msg.text() === 'complete',
    timeout: 10000,
  });

  const err_msg: string = err_msgs.join('\n');
  expect(errors, err_msg).toHaveLength(0);
  expect(err_msgs, err_msg).toHaveLength(0);
});

function nowString() {
    const now = new Date(Date.now());
    const Y = now.getFullYear().toString();
    const M = (now.getMonth() + 1).toString().padStart(2, '0');
    const D = now.getDate().toString().padStart(2, '0');
    const h = now.getHours().toString().padStart(2, '0');
    const m = now.getMinutes().toString().padStart(2, '0');
    const s = now.getSeconds().toString().padStart(2, '0');
    const ms = now.getMilliseconds().toString().padStart(3, '0');
    return `${Y}-${M}-${D} ${h}:${m}:${s}.${ms}`;
}

from __future__ import annotations

from typing import Any

import glob
import hashlib
import html as _html
import json
import logging
import math
import os
import re
import tempfile
import threading
import time
import uuid
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass
from urllib.parse import quote

from jwsgj.diag_guard_io import discard_tmp_file, safe_delete
from jwsgj.diag_guard_state import (
    ProcessLock,
)
from jwsgj.diag_types_defs import (
    ConcurrentExecutionError,
)
from jwsgj.diag_types_normalize import timestamp_ms
from jwsgj.log_config import log_swallowed
from jwsgj.runtime_paths import (
    get_backup_base,
    get_html_report_base,
    json_root_dir,
    stage_json_artifact_path,
)
from jwsgj.runtime_scope import canonical_path, normalize_skill_dir
from jwsgj.xv_intermediate_store import get_round_start_ts

__all__ = [
    "CSS",
    "DEFAULT_SKILL_DIR",
    "JS",
    "SHOW_ALL_HIDDEN_JS",
    "STAGES",
    "STAGE_META",
    "append_stage_section",
    "artifact_root_hint",
    "assert_buttons_complete",
    "emit_final_block",
    "emit_to_stage",
    "ensure_stage_file",
    "extract_fragment",
    "load_stage_json",
    "normalize_skill_key",
    "read_stage_meta",
    "replace_final_block_multi",
    "resolve_stage_file",
    "stage_filename",
    "stage_of_file",
    "stage_pair_status",
    "upgrade_stage_skeleton",
]
STAGE_META = {
    "diag": {"title": "诊断阶段报告", "icon": "🔬"},
    "cv": {"title": "交叉验证阶段报告", "icon": "🧪"},
    "fanout": {"title": "阶段G扇出诊断与治疗报告", "icon": "🌊"},
    "treat_review": {"title": "审核与治疗阶段报告", "icon": "🩹"},
    "retro_feedback": {"title": "复盘与反哺阶段报告", "icon": "🔄"},
    "final": {"title": "全流程最终报告", "icon": "🏁"},
}
STAGES = frozenset(STAGE_META)
logger = logging.getLogger("jwsgj.html_report_stage_doc")
CSS = """
* { margin: 0; padding: 0; box-sizing: border-box; }
:root {
  --primary: #667eea; --primary-dark: #5a67d8; --secondary: #764ba2;
  --success: #38a169; --warning: #dd6b20; --danger: #e53e3e; --info: #3182ce;
  --bg: #f5f7fa; --card-bg: #ffffff; --text: #2d3748; --text-muted: #718096;
  --border: #e2e8f0; --shadow: rgba(0,0,0,0.1); --code-bg: #f7fafc;
  --tab-bg: #e2e8f0; --tab-hover: #cbd5e1;
}
[data-theme="dark"] {
  --bg: #1a202c; --card-bg: #2d3748; --text: #e2e8f0; --text-muted: #a0aec0;
  --border: #4a5568; --shadow: rgba(0,0,0,0.3); --code-bg: #1a202c;
  --tab-bg: #4a5568; --tab-hover: #718096;
}
html { scroll-behavior: smooth; }
body { font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
       background: var(--bg); color: var(--text); line-height: 1.6;
       transition: background 0.3s, color 0.3s; }
.container { max-width: 1400px; margin: 0 auto; padding: 20px; }
.header { background: linear-gradient(135deg, var(--primary) 0%, var(--secondary) 100%);
          color: white; padding: 30px 40px; border-radius: 12px; margin-bottom: 24px;
          box-shadow: 0 4px 6px rgba(0,0,0,0.1); }
.header h1 { font-size: 28px; margin-bottom: 8px; }
.header .meta { font-size: 14px; opacity: 0.9; }
.header .meta .meta-row { margin-top: 4px; word-break: break-all; }
/* 页签吸顶：长报告滚动时章节切换恒可达（空间可操作性）；
   底色随主题防透底 */
.tabs { display: flex; gap: 4px; margin-bottom: 16px; flex-wrap: wrap;
        position: sticky; top: 0; z-index: 900; background: var(--bg);
        padding: 8px 0 10px; }
.tab { padding: 10px 20px; background: var(--tab-bg); border-radius: 8px 8px 0 0;
       cursor: pointer; font-size: 14px; font-weight: 500; transition: all 0.2s;
       border: none; color: var(--text); }
.tab:hover { background: var(--tab-hover); }
.tab.active { background: var(--primary); color: white; }
.tab-content { display: none; background: var(--card-bg); color: var(--text);
               border-radius: 0 12px 12px 12px; padding: 24px;
               box-shadow: 0 2px 4px rgba(0,0,0,0.05); }
.tab-content.active { display: block; }
.card { background: var(--card-bg); color: var(--text); border-radius: 10px;
        padding: 20px; margin-bottom: 16px;
        box-shadow: 0 2px 4px rgba(0,0,0,0.05); border: 1px solid var(--border); }
.card h3 { font-size: 16px; color: var(--text); margin-bottom: 12px; }
.stat-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(160px, 1fr));
             gap: 16px; margin-bottom: 24px; }
.stat { background: var(--card-bg); color: var(--text); border-radius: 10px;
        padding: 20px; text-align: center;
        box-shadow: 0 2px 4px rgba(0,0,0,0.05); border: 1px solid var(--border); }
.stat .value { font-size: 32px; font-weight: 700; color: var(--primary); }
.stat .label { font-size: 13px; color: var(--text-muted); margin-top: 4px; }
.stat.danger .value { color: var(--danger); }
.stat.warning .value { color: var(--warning); }
.stat.success .value { color: var(--success); }
.stat.info .value { color: var(--info); }
.stat.muted .value { color: var(--text-muted); }
table { width: 100%; border-collapse: collapse; font-size: 13px; }
th { text-align: left; padding: 10px 12px; background: var(--code-bg);
     border-bottom: 2px solid var(--border); font-weight: 600;
     color: var(--text); cursor: pointer; }
th:hover { background: var(--border); }
td { padding: 8px 12px; border-bottom: 1px solid var(--border); color: var(--text);
     overflow-wrap: anywhere; }
tr:hover { background: var(--code-bg); }
.badge { display: inline-block; padding: 2px 10px; border-radius: 12px; font-size: 12px;
         font-weight: 600; }
.badge-danger { background: #fed7d7; color: #c53030; }
.badge-warning { background: #feebc8; color: #c05621; }
.badge-info { background: #bee3f8; color: #2c5282; }
.badge-success { background: #c6f6d5; color: #276749; }
.badge-muted { background: var(--border); color: var(--text-muted); }
.progress-bar { width: 100%; height: 8px; background: var(--border); border-radius: 4px; overflow: hidden; }
.progress-fill { height: 100%; border-radius: 4px; transition: width 0.3s; }
.filter-bar { margin-bottom: 16px; }
.filter-bar input { padding: 8px 12px; border: 1px solid var(--border); border-radius: 6px;
                    width: 300px; font-size: 14px; background: var(--card-bg);
                    color: var(--text); }
.collapsible { cursor: pointer; padding: 12px; background: var(--code-bg); border-radius: 6px;
               margin-bottom: 8px; display: flex; justify-content: space-between;
               color: var(--text); }
.collapsible:hover { background: var(--border); }
.collapsible-content { display: none; padding: 12px; }
.collapsible-content.show { display: block; }
.health-badge { font-size: 14px; font-weight: 600; padding: 6px 16px; border-radius: 20px; }
.health-clean, .health-healthy { background: #c6f6d5; color: #22543d; }
.health-warning { background: #feebc8; color: #7b341e; }
.health-critical { background: #fed7d7; color: #822727; }
.footer { text-align: center; padding: 20px; color: #a0aec0; font-size: 12px; }
.severity-P0 { color: var(--danger); font-weight: bold; }
.severity-P1 { color: var(--warning); font-weight: bold; }
.severity-P2 { color: #d69e2e; }
.severity-P3 { color: var(--text-muted); }
/* 渐进披露：超阈值行默认隐藏，点展开钮全量可见（数据零丢弃） */
.row-hidden { display: none; }
.show-more-btn { margin: 8px 0; padding: 6px 14px; border: 1px solid var(--border);
                 border-radius: 6px; background: var(--code-bg); color: var(--text);
                 cursor: pointer; font-size: 13px; }
.show-more-btn:hover { background: var(--border); }
/* 长路径完整展示：不断字符，容器内自动换行（追溯能力保护） */
.path-cell { word-break: break-all; }
/* 值级渐进披露（_disclosure_value）：短值内联，长值 details 折叠全量 */
.val-details { display: block; max-width: 100%; }
.val-summary { cursor: pointer; color: var(--text); list-style: none;
               word-break: break-all; }
.val-summary::-webkit-details-marker { display: none; }
.val-summary::before { content: "▸ "; color: var(--primary); }
.val-details[open] > .val-summary::before { content: "▾ "; }
.val-more { color: var(--primary); font-size: 12px; white-space: nowrap; }
.val-full { white-space: pre-wrap; word-break: break-all; background: var(--code-bg);
            border: 1px solid var(--border); border-radius: 6px; padding: 12px;
            margin-top: 4px; max-height: 480px; overflow: auto;
            font-family: 'Cascadia Code', Consolas, 'Courier New', monospace; font-size: 12px;
            line-height: 1.5; }
/* JSON 交互式查看器 */
.json-viewer { background: var(--code-bg); border: 1px solid var(--border);
               border-radius: 8px; padding: 12px; margin: 8px 0;
               font-family: 'Cascadia Code', Consolas, monospace; font-size: 13px; }
.json-viewer .json-key { color: #9f7aea; font-weight: 500; }
.json-viewer .json-string { color: var(--success); }
.json-viewer .json-number { color: var(--warning); }
.json-viewer .json-bool { color: var(--info); }
.json-viewer .json-null { color: var(--text-muted); font-style: italic; }
.json-viewer .json-bracket { color: var(--primary); font-weight: bold; }
.json-toolbar { display: flex; gap: 8px; margin-bottom: 8px; flex-wrap: wrap;
               /* 吸顶：长 JSON 滚动时操作控件始终可达（空间可操作性） */
               position: sticky; top: 0; z-index: 5;
               background: var(--card-bg); padding: 4px 0; }
.json-btn { padding: 4px 12px; border: 1px solid var(--border); border-radius: 4px;
            background: var(--card-bg); color: var(--text); cursor: pointer;
            font-size: 12px; transition: all 0.2s; }
.json-btn:hover { background: var(--primary); color: white; border-color: var(--primary); }
.json-btn.active { background: var(--primary); color: white; }
.json-content { max-height: 500px; overflow: auto; }
.json-toggle { cursor: pointer; user-select: none; color: var(--text-muted);
               display: inline-block; width: 16px; text-align: center; }
.json-toggle:hover { color: var(--primary); }
.json-collapsed > .json-children { display: none; }
/* JSON 树形查看器（真树形折叠结构）：节点 open/collapsed 两态由
   json-collapsed 类驱动；折叠后显示「… N 键/项 …」摘要与闭括号，
   数据零丢弃（全部留在 DOM，仅视觉隐藏） */
.json-node { display: inline; }
.json-children { display: block; margin-left: 18px;
                 border-left: 1px dashed var(--border); padding-left: 10px; }
.json-row { display: block; padding: 1px 2px; border-radius: 3px; }
.json-row:hover { background: rgba(102,126,234,0.08); }
.json-bracket { color: var(--text-muted); font-weight: 600; }
.json-index { color: var(--text-muted); font-size: 12px; }
.json-ellipsis { display: none; color: var(--text-muted); font-size: 12px;
                 font-style: italic; }
.json-close-inline { display: none; }
.json-node.json-collapsed > .json-children { display: none; }
.json-node.json-collapsed > .json-ellipsis { display: inline; }
.json-node.json-collapsed > .json-close-inline { display: inline; }
.json-node.json-collapsed > .json-close { display: none; }
.json-tree-fallback { display: block; white-space: pre-wrap; word-break: break-all;
                      color: var(--text-muted); font-size: 12px;
                      background: var(--bg); border-radius: 4px; padding: 4px 8px;
                      margin: 2px 0; }
.json-string { word-break: break-all; }
.json-meta { color: var(--text-muted); font-size: 12px; margin-left: auto;
             align-self: center; }
.json-search-count { color: var(--primary); font-size: 12px; align-self: center; }
/* 主题切换按钮 */
.theme-toggle { position: fixed; top: 20px; right: 20px; z-index: 1000;
                padding: 8px 16px; border: none; border-radius: 20px;
                background: var(--card-bg); color: var(--text); cursor: pointer;
                box-shadow: 0 2px 8px var(--shadow); font-size: 14px;
                transition: all 0.3s; }
.theme-toggle:hover { transform: translateY(-2px); box-shadow: 0 4px 12px var(--shadow); }
/* 搜索高亮 */
.search-highlight { background: #faf089; color: #744210; padding: 1px 2px;
                    border-radius: 2px; }
/* 全屏模式 */
.fullscreen-mode .container { max-width: 100%; padding: 10px; }
.fullscreen-toggle { position: fixed; bottom: 20px; right: 20px; z-index: 1000;
                     padding: 10px; border: none; border-radius: 50%;
                     background: var(--primary); color: white; cursor: pointer;
                     box-shadow: 0 2px 8px var(--shadow); width: 44px; height: 44px;
                     display: flex; align-items: center; justify-content: center; }
/* 返回顶部：长报告（多发现项/大 JSON）滚动后一键回顶，与全屏钮
   左底对称布位——默认隐藏，滚动超阈值由 JS 点亮 */
.back-top { position: fixed; bottom: 20px; left: 20px; z-index: 1000;
            padding: 10px; border: none; border-radius: 50%;
            background: var(--secondary); color: white; cursor: pointer;
            box-shadow: 0 2px 8px var(--shadow); width: 44px; height: 44px;
            display: none; align-items: center; justify-content: center;
            font-size: 16px; transition: opacity 0.2s; }
.back-top.show { display: flex; }
/* 响应式优化 */
@media (max-width: 768px) {
  .container { padding: 10px; }
  .stat-grid { grid-template-columns: repeat(2, 1fr); }
  .header { padding: 20px; }
  .header h1 { font-size: 22px; }
}
/* 滚动条美化：细条透明轨道降噪，暗色主题适配（长报告/长 JSON 滚动更顺眼） */
html { scrollbar-width: thin; scrollbar-color: #cbd5e0 transparent; }
[data-theme="dark"] { scrollbar-color: #4a5568 transparent; }
::-webkit-scrollbar { width: 10px; height: 10px; }
::-webkit-scrollbar-track { background: transparent; }
::-webkit-scrollbar-thumb { background: #cbd5e0; border-radius: 5px; }
::-webkit-scrollbar-thumb:hover { background: #a0aec0; }
[data-theme="dark"] ::-webkit-scrollbar-thumb { background: #4a5568; }
[data-theme="dark"] ::-webkit-scrollbar-thumb:hover { background: #718096; }
/* 键盘焦点可见性：Tab 导航到控件时高亮轮廓（可操作性） */
:focus-visible { outline: 2px solid var(--primary); outline-offset: 2px; }
/* 按钮按压反馈：点击瞬间位移，交互确认更直接 */
button:active { transform: translateY(1px); }
/* 打印样式 */
@media print {
  .theme-toggle, .fullscreen-toggle, .json-toolbar { display: none; }
  .val-full { max-height: none; overflow: visible; }
  body { background: white; }
}
"""
SHOW_ALL_HIDDEN_JS = """\
function showAllHidden(elId, btn) {
    var el = document.getElementById(elId);
    if (el) {
        // 元素自身与后代同解除：表格/列表/键值表原语把 id 打在容器上、
        // row-hidden 打在后代行上，只清后代已足够；自解除是为了兼容
        // 「容器自身也带 row-hidden」的调用方（先把 id 容器整体折起再
        // 展开），否则容器恒隐、「显示剩余 N 条」按钮点击失效。
        // 两者并存时零效果零风险。
        el.classList.remove('row-hidden');
        el.querySelectorAll('.row-hidden').forEach(function (n) {
            n.classList.remove('row-hidden');
        });
        // 展开是粘性终态：丢掉行窗口阈值，后续排序不再重新折起尾部
        if (el.hasAttribute && el.hasAttribute('data-jw-hide-from')) {
            el.removeAttribute('data-jw-hide-from');
        }
    }
    if (btn) { btn.style.display = 'none'; }
}
"""
JS = """
function showTab(tabId) {
    document.querySelectorAll('.tab-content').forEach(el => el.classList.remove('active'));
    document.querySelectorAll('.tab').forEach(el => el.classList.remove('active'));
    document.getElementById(tabId).classList.add('active');
    var tabs = document.querySelectorAll('.tab');
    for (var i = 0; i < tabs.length; i++) {
        if (tabs[i].getAttribute('data-tab') === String(tabId)) {
            tabs[i].classList.add('active');
            break;
        }
    }
}
function toggleCollapsible(id) {
    var el = document.getElementById(id);
    el.classList.toggle('show');
}
function _jwRowWindow(table) {
    // 渐进披露阈值的唯一事实源：render_table 把 initial_visible 写进
    // data-jw-hide-from，排序/筛选/展开都读同一处，避免隐藏归属
    // 在不同机制里各记一份（排序后可见区就不是真实 Top-N）
    var raw = table.getAttribute('data-jw-hide-from');
    if (raw === null || raw === '') { return null; }
    var n = parseInt(raw, 10);
    return (isNaN(n) || n < 0) ? null : n;
}
function _jwApplyRowWindow(table) {
    // 按「当前 DOM 次序」重算前 N 条可见：排序挪动行后隐藏集随之移动
    var from = _jwRowWindow(table);
    if (from === null) { return; }
    var rows = table.querySelectorAll(':scope > tbody > tr');
    for (var i = 0; i < rows.length; i++) {
        if (i >= from) { rows[i].classList.add('row-hidden'); }
        else { rows[i].classList.remove('row-hidden'); }
    }
}
function filterTable(inputId, tableId) {
    var input = document.getElementById(inputId).value.toLowerCase();
    var rows = document.getElementById(tableId).querySelectorAll('tbody tr');
    rows.forEach(row => {
        var text = row.textContent.toLowerCase();
        // 命中行写显式 table-row：空内联值会被 .row-hidden{display:none}
        // 盖住，渐进披露区（initial_visible 之后）的行即使命中也不可见；
        // 查询清空时回落空串，把显隐权交回 row-hidden 类
        row.style.display = text.includes(input)
            ? (input ? 'table-row' : '') : 'none';
    });
}
""" + SHOW_ALL_HIDDEN_JS + """\
function sortTable(tableId, colIndex) {
    var table = document.getElementById(tableId);
    var rows = Array.from(table.querySelectorAll('tbody tr'));
    var ascending = table.dataset.sortDir !== 'asc';
    table.dataset.sortDir = ascending ? 'asc' : 'desc';
    rows.sort((a, b) => {
        var aVal = a.cells[colIndex].textContent.trim();
        var bVal = b.cells[colIndex].textContent.trim();
        var aNum = parseFloat(aVal), bNum = parseFloat(bVal);
        if (!isNaN(aNum) && !isNaN(bNum)) return ascending ? aNum - bNum : bNum - aNum;
        return ascending ? aVal.localeCompare(bVal) : bVal.localeCompare(aVal);
    });
    var tbody = table.querySelector('tbody');
    rows.forEach(row => tbody.appendChild(row));
    _jwApplyRowWindow(table);
}

// ========== JSON 交互式查看器 ==========
function toggleJsonNode(el) {
    var parent = el.parentElement;
    parent.classList.toggle('json-collapsed');
    el.textContent = parent.classList.contains('json-collapsed') ? '▸' : '▾';
}
function expandAllJson(containerId) {
    var container = document.getElementById(containerId);
    if (!container) return;
    container.querySelectorAll('.json-collapsed').forEach(function(el) {
        el.classList.remove('json-collapsed');
    });
    container.querySelectorAll('.json-toggle').forEach(function(el) {
        el.textContent = '▾';
    });
}
function collapseAllJson(containerId) {
    var container = document.getElementById(containerId);
    if (!container) return;
    container.querySelectorAll('.json-node').forEach(function(el) {
        if (el.querySelector('.json-children')) {
            el.classList.add('json-collapsed');
        }
    });
    container.querySelectorAll('.json-toggle').forEach(function(el) {
        el.textContent = '▸';
    });
}
function searchJson(containerId, query) {
    var container = document.getElementById(containerId);
    if (!container) return;
    // 搜索域只覆盖可视树，不命中工具栏文本或配套 JSON 文件
    var scope = container.querySelector('.json-content') || container;
    var meta = container.querySelector('.json-search-count');
    // 清除旧高亮
    scope.querySelectorAll('.search-highlight').forEach(function(el) {
        var parent = el.parentNode;
        parent.replaceChild(document.createTextNode(el.textContent), el);
        parent.normalize();
    });
    if (!query) { if (meta) meta.textContent = ''; return; }
    // 字面量子串匹配（indexOf 实现，大小写不敏感）：搜索本意就是
    // 「字面量查词」而非正则检索——正则字面量经 Python 生成 JS 双层
    // 转义，任一层断裂即整块脚本解析失败、页面全部按钮静默失效；
    // indexOf 零转义面零断裂面。
    var needle = String(query).toLowerCase();
    if (!needle) { if (meta) meta.textContent = ''; return; }
    // 先收集后替换：TreeWalker 在 DOM 变更中继续遍历会错位漏命中，
    // 快照为静态列表再逐节点高亮
    var texts = [];
    var walker = document.createTreeWalker(scope, NodeFilter.SHOW_TEXT, null, false);
    while (walker.nextNode()) { texts.push(walker.currentNode); }
    var hits = 0;
    texts.forEach(function(node) {
        var hay = node.nodeValue.toLowerCase();
        var idx = hay.indexOf(needle);
        if (idx < 0) { return; }
        var frag = document.createDocumentFragment();
        var lastIdx = 0;
        while (idx >= 0) {
            frag.appendChild(document.createTextNode(node.nodeValue.slice(lastIdx, idx)));
            var mark = document.createElement('mark');
            mark.className = 'search-highlight';
            mark.textContent = node.nodeValue.slice(idx, idx + needle.length);
            frag.appendChild(mark);
            hits++;
            lastIdx = idx + needle.length;
            idx = hay.indexOf(needle, lastIdx);
        }
        frag.appendChild(document.createTextNode(node.nodeValue.slice(lastIdx)));
        node.parentNode.replaceChild(frag, node);
    });
    // 命中点所在折叠节点自动展开：高亮打在不可见子树=假无结果，
    // 展开祖先后命中即刻可视
    scope.querySelectorAll('.search-highlight').forEach(function(h) {
        var p = h.parentElement;
        while (p && p !== scope) {
            if (p.classList && p.classList.contains('json-collapsed')) {
                p.classList.remove('json-collapsed');
                var t = p.querySelector(':scope > .json-toggle');
                if (t) t.textContent = '\u25be';
            }
            p = p.parentElement;
        }
    });
    if (meta) { meta.textContent = hits ? ('命中 ' + hits + ' 处') : '无匹配'; }
}

// ========== 主题切换 ==========
function _themeStorageGet() {
    // 隐私模式/沙箱 iframe（opaque origin）下访问 localStorage 即抛
    // SecurityError；不守卫会击穿 initTheme，连带其后的返回顶部监听
    // 注册一并中断（整块初始化静默失效）
    try {
        return window.localStorage ? window.localStorage.getItem('html-report-theme') : null;
    } catch (e) { return null; }
}
function _themeStorageSet(value) {
    // 存储只做偏好持久化，写失败不影响本次主题生效（同 get 守卫口径）
    try {
        if (window.localStorage) { window.localStorage.setItem('html-report-theme', value); }
    } catch (e) { return; }
}
function toggleTheme() {
    var html = document.documentElement;
    var current = html.getAttribute('data-theme');
    var next = current === 'dark' ? 'light' : 'dark';
    html.setAttribute('data-theme', next);
    _themeStorageSet(next);
    var btn = document.querySelector('.theme-toggle');
    if (btn) btn.textContent = next === 'dark' ? '☀️ 浅色' : '🌙 深色';
}
function initTheme() {
    var saved = _themeStorageGet();
    var prefersDark = window.matchMedia('(prefers-color-scheme: dark)').matches;
    var theme = saved || (prefersDark ? 'dark' : 'light');
    document.documentElement.setAttribute('data-theme', theme);
    var btn = document.querySelector('.theme-toggle');
    if (btn) btn.textContent = theme === 'dark' ? '☀️ 浅色' : '🌙 深色';
}

// ========== 全屏模式 ==========
function toggleFullscreen() {
    document.body.classList.toggle('fullscreen-mode');
    var btn = document.querySelector('.fullscreen-toggle');
    if (btn) btn.textContent = document.body.classList.contains('fullscreen-mode') ? '✕' : '⛶';
}

// ========== 返回顶部与条目底收 ==========
function scrollToTop() { window.scrollTo({top: 0, behavior: 'smooth'}); }
function _jwCollapseItem(btn) {
    // 阶段聚合条目底收钮：超长条目展开后滚回页首成本极高，底部一键
    // 收拢并回滚锚定条目头（只作用于所属 details，不误触兄弟条目）
    var d = btn.closest('details.jw-item');
    if (!d) { d = btn.closest('details'); }
    if (d) { d.open = false; d.scrollIntoView({behavior: 'smooth', block: 'start'}); }
}

// ========== 初始化 ==========
document.addEventListener('DOMContentLoaded', function() {
    initTheme();
    // 返回顶部按钮滚动点亮：滚动超阈值才显示，不遮蔽首屏内容
    window.addEventListener('scroll', function() {
        var btn = document.querySelector('.back-top');
        if (btn) { btn.classList.toggle('show', window.scrollY > 400); }
    });
});
"""
_DEFAULT_ITEM_ICON = "📄"
# skill_dir 参数的统一默认哨兵（空串 = 运行时经 normalize_skill_dir 解析），
# 供 html_render_pipeline 等上游渲染模块复用，避免各自重复定义。
DEFAULT_SKILL_DIR = ""
_DEFAULT_SKILL_DIR = DEFAULT_SKILL_DIR
_DEFAULT_ROUND_TS = ""
_DEFAULT_MID = ""
# 报告文件统一走「中文语义名 + 17 位时间戳」口径（年月日时分秒毫秒），
# 例如 诊断A20261121104830438.html / 诊断A20261121104830438.json。
# 中文名直接可读，时间戳保证同秒内多次运行不互相覆盖且可按名排序定位。
_FINAL_REPORT_STEM = "最终报告"
_FINAL_REPORT_PREFIX = _FINAL_REPORT_STEM
_FINAL_FIXED_NAME = f"{_FINAL_REPORT_STEM}.html"
_STAGE_REV = "4"
_META_RE = re.compile(
    r'<!--JW-META stage="([^"]*)" skill="([^"]*)" round="([^"]*)"'
    r'(?: rev="([^"]*)")?(?: generated="([^"]*)")?-->')
_APPEND_MARKER = "<!--JW_STAGE_APPEND-->"
_FINAL_ANCHOR = "<!--JW_FINAL_ANCHOR-->"
_FINAL_BLOCK_END = "<!--JW_FINAL_BLOCK_END-->"
_CONTROL_MARKERS = (_APPEND_MARKER, _FINAL_ANCHOR, _FINAL_BLOCK_END)
_COUNT_PATTERN = r'(<span id="jw-item-count">)(\d+)(</span>)'
_COUNT_RE = re.compile(_COUNT_PATTERN)
_COUNT_BYTES_RE = re.compile(_COUNT_PATTERN.encode("utf-8"))
_ITEM_KEY_RE = re.compile(r"<!--JW_ITEM_KEY:([^>]+)-->")
_ITEM_OPEN_TAG = '<details class="jw-item">'
_ITEM_BLOCK_RE = re.compile(
    re.escape(_ITEM_OPEN_TAG) + r'\s*<!--JW_ITEM_KEY:([^>]+)-->\s*'
    r'<summary>(.*?)<span class="jw-item-ts">', re.DOTALL)
_MARK_BYTES = _APPEND_MARKER.encode("utf-8")
_STAGE_CSS = """
details.jw-item{margin:14px 0;border:1px solid #e2e8f0;border-radius:8px;overflow:hidden}
details.jw-item>summary{cursor:pointer;padding:10px 14px;background:#f7fafc;
font-weight:600;list-style:none;color:#2d3748}
details.jw-item>summary::-webkit-details-marker{display:none}
details.jw-item>summary::before{content:"\\25B8 ";color:#718096}
details.jw-item[open]>summary::before{content:"\\25BE "}
span.jw-item-ts{float:right;font-weight:400;color:#a0aec0;font-size:12px}
div.jw-item-body{padding:4px 14px 14px;border-top:1px solid #edf2f7}
.jw-item-body .tabs{display:none}
.jw-item-body .tab-content{display:block!important;padding:6px 0;border:none}
.jw-item-body .container{max-width:none;padding:0;margin:0;box-shadow:none;border:none}
/* 条目已有自己的 summary 标题与时间戳：渲染页面的页头再出现一次就是
   每个条目重复整份报告头（标题/元信息/渐变背景）。 */
.jw-item-body .header{display:none}
.jw-item-body .footer{display:none}
.jw-controls{margin:10px 0 2px;display:flex;gap:8px;align-items:center;flex-wrap:wrap}
.jw-controls button{cursor:pointer;padding:6px 14px;border:1px solid #cbd5e0;
border-radius:6px;background:#edf2f7;color:#2d3748;font-size:13px}
.jw-controls button:hover{background:#e2e8f0}
.jw-controls .jw-controls-hint{color:#a0aec0;font-size:12px}
/* 条目底收钮：长条目展开后的底部一键收拢（与页首 summary 双点可达） */
.jw-collapse-bottom{display:block;text-align:center;padding:8px;margin-top:10px;
color:#667eea;cursor:pointer;font-size:13px;user-select:none;
border-top:1px dashed #e2e8f0}
.jw-collapse-bottom:hover{background:#f7fafc;text-decoration:underline}
"""
_STAGE_JS = ("""<script>
function _jwSetAllItems(open){
  document.querySelectorAll('details.jw-item').forEach(function(d){d.open=open;});
  document.querySelectorAll('details.jw-item details').forEach(function(d){d.open=open;});
}
""" + JS + """</script>
""")
def _path_arg(value) -> str:
    if value is None:
        return ""
    try:
        return os.fsdecode(value)
    except TypeError:
        return ""
def _text_of(value) -> str:
    return "" if value is None else str(value)
def _utf8_bytes(value) -> bytes:
    return _text_of(value).encode("utf-8", errors="backslashreplace")
def load_stage_json(html_path: str, skill_dir: str = _DEFAULT_SKILL_DIR) -> dict:
    html_path = _path_arg(html_path)
    if not html_path:
        return {}
    try:
        path = stage_json_artifact_path(html_path, skill_dir)
        with open(path, encoding="utf-8-sig") as handle:
            payload = json.load(handle)
        return payload if isinstance(payload, dict) else {}
    except (OSError, RuntimeError, ValueError, RecursionError) as exc:
        log_swallowed(__name__, exc, context="load_stage_json:read")
        return {}
def _stage_item_snapshots(doc: str) -> dict[str, dict[str, str]]:
    snapshots: dict[str, dict[str, str]] = {}
    for key, summary in _ITEM_BLOCK_RE.findall(doc):
        text = _html.unescape(re.sub(r"<[^>]+>", "", summary)).strip()
        icon, _, title = text.partition(" ")
        snapshots[key] = {
            "title": title or text,
            "icon": icon or _DEFAULT_ITEM_ICON,
        }
    return snapshots
def _valid_count(value) -> int | None:
    return value if isinstance(value, int) and not isinstance(value, bool) else None
def stage_pair_status(html_path: str, skill_dir: str = _DEFAULT_SKILL_DIR) -> dict:
    html_path = _path_arg(html_path)
    if not html_path:
        return {"json_path": "", "html_items": 0, "json_items": None,
                "status": "missing"}
    try:
        json_path = stage_json_artifact_path(html_path, skill_dir)
    except (OSError, RuntimeError, ValueError) as exc:
        log_swallowed(__name__, exc, context="stage_pair_status:path")
        return {"json_path": "", "html_items": 0, "json_items": None,
                "status": "missing"}
    html_exists = os.path.isfile(html_path)
    html_doc = _read_stage_doc(html_path) if html_exists else ""
    html_count = len(_extract_stage_items(html_doc, 0))
    html_snapshots = _stage_item_snapshots(html_doc)
    exists = os.path.isfile(json_path)
    payload = load_stage_json(html_path, skill_dir) if exists else {}
    json_count = _valid_count(payload.get("item_count")) if payload else None
    items = payload.get("items") if payload else None
    if not html_exists or not exists:
        status = "missing"
    elif (not html_doc
          or json_count is None
          or not isinstance(items, dict)
          or any(not isinstance(item, dict) for item in items.values())
          or len(html_snapshots) != html_count):
        status = "invalid"
    elif (json_count != html_count or len(items) != html_count
          or set(html_snapshots) != set(items)):
        status = "mismatch"
    else:
        status = "paired"
    return {
        "json_path": json_path if exists else "",
        "html_items": html_count,
        "json_items": json_count,
        "status": status,
    }
def artifact_root_hint(skill_dir: str = _DEFAULT_SKILL_DIR) -> str:
    try:
        return json_root_dir(skill_dir or None)
    except Exception as _e:
        log_swallowed(__name__, _e, context="artifact_root_hint:Exc")
        return ""
def _under_system_temp(path: str) -> bool:
    """判定路径是否位于系统临时目录之下（沙箱锚点识别）。

    历史缺陷：直接用 ``os.path.commonpath([target, root])`` 比较。工作区在
    ``D:`` 而系统临时目录在 ``C:`` 时，``commonpath`` 抛
    ``ValueError: Paths don't have the same drive``，被吞后返回 False——
    于是「临时目录下的沙箱技能」与「真实工作区」无法区分，阶段报告落到真实
    工作区（实测污染 ``htm/`` 与 ``zhenduan/``，并让 ``doc_refactor_apply``
    以相对路径 ``test`` 报「源 SKILL.md 不存在」）。

    跨盘必然不在临时目录下，先按驱动器短路，再做前缀比较。
    """
    if not path:
        return False
    try:
        root = os.path.normcase(canonical_path(tempfile.gettempdir()))
        target = os.path.normcase(canonical_path(path))
    except (OSError, ValueError) as _canon_exc:
        log_swallowed(__name__, _canon_exc,
                      context=f'_under_system_temp:{type(_canon_exc).__name__}')
        return False
    if os.path.splitdrive(root)[0] != os.path.splitdrive(target)[0]:
        return False
    try:
        return os.path.commonpath([target, root]) == root
    except (OSError, ValueError) as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc,
                      context=f'_under_system_temp:{type(_swallowed_exc).__name__}')
        return False
def _is_sandbox_skill_anchor(skill_dir: str, html_base: str = "") -> bool:
    if not _under_system_temp(skill_dir):
        return False
    return not _under_system_temp(html_base) if html_base else True
def _round_ts(skill_dir: str) -> str:
    try:
        ts = get_round_start_ts(skill_dir or "")
        if isinstance(ts, str) and len(ts) == 17 and ts.isdecimal():
            return ts
    except Exception as _rte:
        logger.debug("[Stage] 轮次 ts 解析失败(降级新 ts): %s", _rte)
    return ""
# 阶段中文名词干：诊断方法按 A–F 字母区分（诊断A…诊断F），扇出固定为 G。
_STAGE_FILE_LABELS = {
    "diag": "诊断",
    "cv": "交叉验证",
    "fanout": "扇出G",
    "treat_review": "审核治疗",
    "retro_feedback": "复盘反哺",
    "final": _FINAL_REPORT_PREFIX,
}
# 旧英文前缀：历史产物只读兼容（能识别、配对、清理），新产物不再生成。
_LEGACY_STAGE_PREFIXES = {
    "diag": ("diag_stage_",),
    "cv": ("cv_report_",),
    "fanout": ("stage_fanout_",),
    "treat_review": ("stage_treat_review_",),
    "retro_feedback": ("stage_retro_feedback_",),
    "final": ("final_report_",),
}
def _stage_prefix(stage: str) -> str:
    return _STAGE_FILE_LABELS.get(stage, f"stage_{_safe_stage_token(stage)}_")
_STAGE_TOKEN_UNSAFE_RE = re.compile(r"[^A-Za-z0-9_.-]+")
_MID_LETTER_RE = re.compile(r"[A-Za-z]")
def _safe_stage_token(value: str, fallback: str = "") -> str:
    token = _STAGE_TOKEN_UNSAFE_RE.sub("_", str(value or "")).strip("._")
    return token or fallback
def _mid_token(mid: str) -> str:
    """诊断方法字母（A–F）直接拼在中文名后，其余 mid 走安全 token。"""
    token = str(mid or "").strip()
    if not token:
        return ""
    if _MID_LETTER_RE.fullmatch(token):
        return token.upper()
    return _safe_stage_token(token)
def _resolve_round_token(round_ts: str) -> str:
    return _safe_stage_token(round_ts) or timestamp_ms()
def stage_filename(stage: str, round_ts: str, mid: str = _DEFAULT_MID, *,
                   owner: str = "", wildcard: bool = False) -> str:
    ts = "*" if wildcard else _resolve_round_token(round_ts)
    # 通配只放开时间戳与 owner，方法字母必须保留：否则诊断A–F 会互相
    # 命中同一个阶段文件，六个方法被合并成一份。
    mid_token = _mid_token(mid)
    owner_token = _safe_stage_token(owner)
    owner_part = f"{owner_token}_" if owner_token and not wildcard else ""
    return f"{_stage_prefix(stage)}{mid_token}{owner_part}{ts}.html"
def stage_of_file(filename: str) -> str:
    base = os.path.basename(_path_arg(filename))
    if not base:
        return ""
    if base == _FINAL_FIXED_NAME or base.startswith(_FINAL_REPORT_PREFIX):
        return "final"
    for stage in STAGE_META:
        if stage != "final" and base.startswith(_stage_prefix(stage)):
            return stage
    # 旧英文前缀只读兼容：历史 diag_stage_/cv_report_/stage_*_ 仍可定位阶段。
    for stage, prefixes in _LEGACY_STAGE_PREFIXES.items():
        if any(base.startswith(prefix) for prefix in prefixes):
            return stage
    if base.startswith("diag_"):
        return "diag"
    return ""
_HEAD_WINDOW = 4096
def _read_head(path: str, limit: int = _HEAD_WINDOW) -> str:
    path = _path_arg(path)
    if not path:
        return ""
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            return f.read(limit)
    except FileNotFoundError:
        return ""
    except OSError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_read_head:OSError')
        return ""
def round_ts_human(round_ts: str) -> str:
    """17 位毫秒戳 → 人类可读时间；无法解析时返回空串。

    报告文件名里的时间戳是「轮次开始时刻」，不是「报告生成时刻」。
    两者可能相差整轮耗时（实测可达 16 分钟），页头必须同时给出两个
    时刻，读者才不会把轮次起点误读成报告新鲜度。
    """
    _t = str(round_ts or "").strip()
    if len(_t) == 17 and _t.isdecimal():
        return (f"{_t[0:4]}-{_t[4:6]}-{_t[6:8]} "
                f"{_t[8:10]}:{_t[10:12]}:{_t[12:14]}")
    return ""
def _meta_of(head: str) -> dict:
    m = _META_RE.search(head)
    if not m:
        return {}
    return {"stage": m.group(1), "skill": _html.unescape(m.group(2)),
            "round": _html.unescape(m.group(3)), "rev": m.group(4),
            "generated": m.group(5) or ""}
def read_stage_meta(path: str) -> dict:
    return _meta_of(_read_head(path))
def _norm_sd(skill_dir: str) -> str:
    skill_dir = _path_arg(skill_dir)
    if not skill_dir:
        return ""
    try:
        return normalize_skill_dir(skill_dir)
    except Exception as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_norm_sd:Exc')
        return skill_dir
def normalize_skill_key(skill_dir: str) -> str:
    return os.path.normcase(_norm_sd(skill_dir))
def _file_skill_ok(head: str, skill_dir: str) -> bool:
    target = normalize_skill_key(skill_dir)
    meta = _meta_of(head)
    if not meta:
        return not target
    owner = normalize_skill_key(meta.get("skill") or "")
    if not target:
        return not owner
    return bool(owner) and owner == target
def _file_round(head: str) -> str:
    return _meta_of(head).get("round", "")
def _filename_round(path: str) -> str:
    """从文件名提取 17 位时间戳（中文名前缀后无下划线也成立）。"""
    match = re.search(r"(\d{17})$", os.path.splitext(
        os.path.basename(path))[0])
    return match.group(1) if match else ""
def _newline_of(data: bytes) -> str:
    return "\r\n" if b"\r\n" in data else "\n"
def _write_text_soft(path: str, text: str, op: str, *,
                     newline: str = "\n") -> bool:
    data = _text_of(text).replace("\r\n", "\n").replace("\r", "\n")
    if newline != "\n":
        data = data.replace("\n", newline)
    try:
        _atomic_write_bytes(path, _utf8_bytes(data))
        return True
    except OSError as e:
        logger.warning("[Stage] %s(不阻断): %s: %s", op, path, e)
        return False
def _companion_link_html(html_path: str, skill_dir: str) -> str:
    if not html_path:
        return ""
    try:
        json_path = stage_json_artifact_path(html_path, skill_dir)
        rel = os.path.relpath(json_path, os.path.dirname(html_path)).replace(os.sep, "/")
    except (OSError, RuntimeError, ValueError) as exc:
        log_swallowed(__name__, exc, context="companion_link:resolve")
        return ""
    name = _html.escape(os.path.basename(json_path))
    href = _html.escape(
        quote(rel, safe="/", errors="backslashreplace"), quote=True)
    return (f'<div class="meta">配套 JSON: <a href="{href}" '
            f'style="color:white;text-decoration:underline">{name}</a></div>')
def _skeleton(stage: str, skill_dir: str, round_ts: str, mid: str = _DEFAULT_MID,
              html_path: str = "") -> str:
    meta = STAGE_META[stage]
    title = meta["title"] + (f"（方法 {mid}）" if mid else "")
    skill_esc = _html.escape(_norm_sd(skill_dir), quote=True)
    round_esc = _html.escape(round_ts, quote=True)
    rev_esc = _html.escape(_STAGE_REV, quote=True)
    _generated_ms = timestamp_ms()
    _generated_human = time.strftime("%Y-%m-%d %H:%M:%S")
    _round_human = round_ts_human(round_ts)
    _round_display = (
        f"{round_esc}（开始于 {_round_human}）" if _round_human
        else (round_esc or "（非管线上下文）"))
    final_anchor = (_FINAL_ANCHOR + _FINAL_BLOCK_END + "\n"
                    if stage == "final" else "")
    companion_link = _companion_link_html(html_path, skill_dir)
    return f"""<!DOCTYPE html>
<html lang="zh-CN">
<!--JW-META stage="{stage}" skill="{skill_esc}" round="{round_esc}" rev="{rev_esc}" generated="{_generated_ms}"-->
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>{_html.escape(title)}</title>
<style>{_stage_style_block()}</style>
</head>
<body data-stage="{stage}" data-skill="{skill_esc}" data-round="{round_esc}">
<button class="theme-toggle" onclick="toggleTheme()">🌙 深色</button>
<button class="fullscreen-toggle" onclick="toggleFullscreen()">⛶</button>
<button class="back-top" onclick="scrollToTop()" title="返回顶部">↑</button>
<div class="container">
<div class="header">
<h1>{meta["icon"]} {_html.escape(title)}</h1>
<div class="meta">目标技能: {skill_esc} | 轮次: {_round_display} | 生成于: {_generated_human}</div>
{companion_link}
</div>
<div class="jw-controls">
<button type="button" onclick="_jwSetAllItems(true)">\u25BC 展开全部条目</button>
<button type="button" onclick="_jwSetAllItems(false)">\u25B8 收起全部条目</button>
<span class="jw-controls-hint">条目内表格「显示剩余 N 条」按钮已恢复可用</span>
</div>
<div id="jw-stage-sections">
{final_anchor}{_APPEND_MARKER}
</div>
<div class="footer">由阶段聚合引擎生成 · 共 <span id="jw-item-count">0</span> 项 · 条目按产生次序追加</div>
</div>
{_STAGE_JS}</body>
</html>"""
def _stage_style_block() -> str:
    return f"{CSS}\n{_STAGE_CSS}"
_STYLE_RE = re.compile(r"<style([^>]*)>(.*?)</style>", re.DOTALL | re.IGNORECASE)
_BODY_RE = re.compile(r"<body[^>]*>(.*?)</body>", re.DOTALL | re.IGNORECASE)
_SCRIPT_RE = re.compile(r"<script[^>]*>.*?</script>", re.DOTALL | re.IGNORECASE)
_JS_FUNC_RE = re.compile(r"function\s+([A-Za-z_$][\w$]*)\s*\(")
_SKELETON_JS_FUNCS = frozenset(_JS_FUNC_RE.findall(_STAGE_JS))
_BUTTON_BLOCK_RE = re.compile(
    r'<button\b[^>]*>.*?</button\s*>', re.DOTALL | re.IGNORECASE)
_BUTTON_OPEN_RE = re.compile(
    r'\A<button\b[^>]*>', re.DOTALL | re.IGNORECASE)
_BUTTON_CLASS_RE = re.compile(
    r'(?<![\w-])class=(["\'])(.*?)\1', re.DOTALL | re.IGNORECASE)
_CHROME_BUTTON_CLASSES = frozenset({
    "theme-toggle", "fullscreen-toggle", "back-top",
})
_STANDARD_STYLE_BLOCKS = frozenset({
    CSS.strip(),
    _stage_style_block().strip(),
})
def _private_styles(doc: str) -> str:
    styles = []
    for sm in _STYLE_RE.finditer(doc):
        attrs, css = sm.group(1), sm.group(2)
        if css.strip() and css.strip() not in _STANDARD_STYLE_BLOCKS:
            styles.append(f"<style{attrs}>{css}</style>")
    return "".join(styles)
def _audit_foreign_functions(body: str) -> None:
    _foreign: set[str] = set()
    for _sm in _SCRIPT_RE.finditer(body):
        for _fn in _JS_FUNC_RE.findall(_sm.group(0)):
            if _fn not in _SKELETON_JS_FUNCS:
                _foreign.add(_fn)
    if _foreign:
        logger.warning("[Stage] 渲染产物 body 内 script 定义非骨架函数 "
                       "%s——剥离后回调将失效，须收编进 JS 全集",
                       sorted(_foreign))
def _escape_control_markers(fragment: str) -> str:
    for marker in _CONTROL_MARKERS:
        fragment = fragment.replace(marker, _html.escape(marker, quote=False))
    return _ITEM_KEY_RE.sub(
        lambda m: _html.escape(m.group(0), quote=False), fragment)
def _strip_chrome_buttons(body: str) -> str:
    def _strip(match: re.Match[str]) -> str:
        block = match.group(0)
        opening = _BUTTON_OPEN_RE.match(block)
        class_attr = (_BUTTON_CLASS_RE.search(opening.group(0))
                      if opening else None)
        if class_attr and not _CHROME_BUTTON_CLASSES.isdisjoint(
                class_attr.group(2).split()):
            return ""
        return block
    return _BUTTON_BLOCK_RE.sub(_strip, body)
def extract_fragment(rendered_html: str) -> str:
    doc = str(rendered_html or "")
    style_html = _private_styles(doc)
    doc = _STYLE_RE.sub("", doc)
    bm = _BODY_RE.search(doc)
    body = bm.group(1) if bm else doc
    body = _strip_chrome_buttons(body)
    _audit_foreign_functions(doc)
    body = _SCRIPT_RE.sub("", body)
    return _escape_control_markers(style_html + body.strip())
def _rev_needs_upgrade(meta: dict) -> bool:
    if not meta:
        return False
    rev = meta.get("rev")
    if not rev:
        return True
    try:
        return int(rev) < int(_STAGE_REV)
    except ValueError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_rev_needs_upgrade:ValueError')
        return True
_DETAILS_TOKEN_RE = re.compile(
    r'<!--.*?(?:-->|$)|<details(?=[\s>])|</details\s*>', re.DOTALL)
_TITLE_MID_RE = re.compile(r"（方法 ([^）]*)）")
def _mid_from_doc(doc: str) -> str:
    match = _TITLE_MID_RE.search(doc[:_HEAD_WINDOW])
    return _html.unescape(match.group(1)) if match else ""
def _details_block_end(doc: str, start: int) -> int:
    depth = 0
    for m in _DETAILS_TOKEN_RE.finditer(doc, start):
        token = m.group(0)
        if token.startswith('<!--'):
            continue
        depth += 1 if token.startswith('<details') else -1
        if depth == 0:
            return m.end()
    return -1
def _extract_stage_items(doc: str, scan_from: int = 0) -> list[str]:
    items: list[str] = []
    idx = scan_from
    while True:
        start = doc.find(_ITEM_OPEN_TAG, idx)
        if start < 0:
            break
        end = _details_block_end(doc, start)
        if end < 0:
            break
        items.append(doc[start:end])
        idx = end
    return items
def _extract_final_block(doc: str) -> str:
    a = doc.find(_FINAL_ANCHOR)
    e = doc.find(_FINAL_BLOCK_END)
    if a < 0 or e < 0 or a > e:
        return ""
    return doc[a + len(_FINAL_ANCHOR):e]
def _skeleton_js_complete(doc: str) -> bool:
    present: set[str] = set()
    for _sm in _SCRIPT_RE.finditer(doc):
        present.update(_JS_FUNC_RE.findall(_sm.group(0)))
    return _SKELETON_JS_FUNCS <= present
def _stage_items_start(doc: str, stage: str) -> int:
    if stage != "final":
        return 0
    end = doc.find(_FINAL_BLOCK_END)
    return end + len(_FINAL_BLOCK_END) if end >= 0 else 0
def _rebuild_stage_doc(path: str, doc: str, stage: str, skill_dir: str,
                       round_ts: str, mid: str) -> tuple[str, int]:
    items = _extract_stage_items(doc, _stage_items_start(doc, stage))
    final_block = _extract_final_block(doc) if stage == "final" else ""
    fresh = _skeleton(stage, skill_dir, round_ts, mid, html_path=path)
    if doc.startswith("\ufeff"):
        fresh = "\ufeff" + fresh
    if final_block:
        fresh = fresh.replace(
            _FINAL_ANCHOR + _FINAL_BLOCK_END,
            _FINAL_ANCHOR + final_block + _FINAL_BLOCK_END, 1)
    if items:
        fresh = fresh.replace(
            _APPEND_MARKER, "".join(it + "\n" for it in items) + _APPEND_MARKER, 1)
    return _recount_items(fresh)
def _skeleton_structure_complete(doc: str, stage: str) -> bool:
    if _APPEND_MARKER not in doc or _last_count_match(doc) is None:
        return False
    if stage == "final":
        anchor = doc.find(_FINAL_ANCHOR)
        block_end = doc.find(_FINAL_BLOCK_END)
        if anchor < 0 or block_end < anchor:
            return False
    return True
def _should_upgrade(doc: str, meta: dict, path: str) -> bool:
    if not meta:
        return False
    if _rev_needs_upgrade(meta):
        return True
    if not _skeleton_js_complete(doc):
        logger.info("[Stage] rev 达标但函数集不全，按内容口径升级骨架: %s", path)
        return True
    file_stage = stage_of_file(path)
    meta_stage = meta.get("stage") or file_stage
    if file_stage and meta_stage != file_stage:
        logger.info("[Stage] 文件名与元数据阶段不一致，按文件名重建骨架: %s", path)
        return True
    stage = file_stage or meta_stage
    if not _skeleton_structure_complete(doc, stage):
        logger.info("[Stage] rev 达标但控制锚点不全，按内容口径升级骨架: %s", path)
        return True
    return False
def _stage_upgrade_context(meta: dict, path: str, skill_dir: str,
                           round_ts: str) -> tuple[str, str, str]:
    stage = stage_of_file(path) or meta.get("stage") or ""
    if stage not in STAGE_META:
        stage = "diag"
    return (stage,
            skill_dir or meta.get("skill") or "",
            round_ts or meta.get("round") or "")
def upgrade_stage_skeleton(path: str, skill_dir: str = _DEFAULT_SKILL_DIR,
                           round_ts: str = _DEFAULT_ROUND_TS, mid: str = _DEFAULT_MID) -> bool:
    path = _path_arg(path)
    if not path:
        logger.warning("[Stage] 骨架升级缺少文件路径（跳过）")
        return False
    data = _read_bytes(path)
    if data is None:
        return False
    newline = _newline_of(data)
    try:
        doc = data.decode("utf-8")
    except UnicodeDecodeError as _decode_e:
        logger.warning("[Stage] 文件非 UTF-8，跳过骨架升级（保留原文件）: %s: %s",
                       path, _decode_e)
        return False
    head = doc[:_HEAD_WINDOW]
    meta = _meta_of(head)
    if not _should_upgrade(doc, meta, path):
        return True
    if not mid:
        mid = _mid_from_doc(doc)
    stage, skill_dir, round_ts = _stage_upgrade_context(
        meta, path, skill_dir, round_ts)
    fresh, _count = _rebuild_stage_doc(
        path, doc, stage, skill_dir, round_ts, mid)
    if not _write_text_soft(path, fresh, "骨架升级失败", newline=newline):
        return False
    logger.info("[Stage] 旧骨架文件已升级至 rev%s（保 %d 条目）: %s",
                _STAGE_REV, _count, path)
    return True
def assert_buttons_complete(doc: str) -> list[str]:
    doc = _text_of(doc)
    used: set[str] = set()
    for m in re.finditer(r'(?<![\w-])on\w+=(?:"|\')\s*([a-zA-Z_]\w*)\s*\(', doc):
        used.add(m.group(1))
    defined: set[str] = set()
    for sm in _SCRIPT_RE.finditer(doc):
        defined.update(_JS_FUNC_RE.findall(sm.group(0)))
    return sorted(used - defined)
_ID_DEF_RE = re.compile(r'(?<![\w-])id=["\']([^"\']+)["\']')
_ON_ATTR_RE = re.compile(r'(?<![\w-])on\w+=(?:"[^"]*"|\'[^\']*\')')
_NS_SINGLE_ID_ATTRS = ("id", "data-tab", "for")
_NS_IDREF_ATTRS = ("aria-labelledby", "aria-describedby", "aria-controls",
                   "aria-owns", "aria-activedescendant")
_NS_ID_ATTR_NAMES = "|".join(_NS_SINGLE_ID_ATTRS + _NS_IDREF_ATTRS)
_NS_ATTR_RE = re.compile(
    r'(?<![\w-])(' + _NS_ID_ATTR_NAMES + r')=(["\'])([^"\']*)\2')
_NS_HREF_RE = re.compile(r'(?<![\w-])href=(["\'])#([^"\']*)\1')
def _id_pairs(fragment: str, prefix: str) -> list[tuple[str, str]]:
    ids: list[str] = []
    for m in _ID_DEF_RE.finditer(fragment):
        x = m.group(1)
        if x and x not in ids:
            ids.append(x)
    ids.sort(key=len, reverse=True)
    return [(x, f"{prefix}_{x}") for x in ids]
def _map_idref_list(value: str, mapping: dict[str, str]) -> str:
    return " ".join(mapping.get(t, t) for t in value.split())
def _rewrite_id_refs(fragment: str, pairs: list[tuple[str, str]]) -> str:
    mapping = dict(pairs)
    def _attr(m: re.Match[str]) -> str:
        name, value = m.group(1), m.group(3)
        if name in _NS_IDREF_ATTRS:
            value = _map_idref_list(value, mapping)
        else:
            value = mapping.get(value, value)
        return f'{name}="{value}"'
    def _href(m: re.Match[str]) -> str:
        return f'href="#{mapping.get(m.group(2), m.group(2))}"'
    return _NS_HREF_RE.sub(_href, _NS_ATTR_RE.sub(_attr, fragment))
def _rewrite_handler_refs(attr: str, pairs: list[tuple[str, str]]) -> str:
    for x, nx in pairs:
        attr = attr.replace(f"'{x}'", f"'{nx}'")
        attr = attr.replace(f'"{x}"', f'"{nx}"')
        attr = attr.replace(f"&quot;{x}&quot;", f"&quot;{nx}&quot;")
        attr = attr.replace(f"&#34;{x}&#34;", f"&#34;{nx}&#34;")
        attr = attr.replace(f"&#x27;{x}&#x27;", f"&#x27;{nx}&#x27;")
        attr = attr.replace(f"&#39;{x}&#39;", f"&#39;{nx}&#39;")
    return attr
def _namespace_fragment_ids(fragment: str, prefix: str) -> str:
    pairs = _id_pairs(fragment, prefix)
    if not pairs:
        return fragment
    out = _rewrite_id_refs(fragment, pairs)
    return _ON_ATTR_RE.sub(
        lambda m: _rewrite_handler_refs(m.group(0), pairs), out)
def _wrap_item(title: str, fragment: str,
               icon: str = _DEFAULT_ITEM_ICON, *, item_key: str = "",
               namespace_ids: bool = True) -> str:
    ts = time.strftime("%Y-%m-%d %H:%M:%S")
    frag = (_namespace_fragment_ids(fragment, f"jwi{uuid.uuid4().hex[:8]}")
            if namespace_ids else fragment)
    key_marker = (f"<!--JW_ITEM_KEY:{item_key}-->\n" if item_key else "")
    return (f'{_ITEM_OPEN_TAG}\n{key_marker}<summary>'
            f'{_html.escape(_text_of(icon))} {_html.escape(_text_of(title))}'
            f'<span class="jw-item-ts">{ts}</span></summary>\n'
            f'<div class="jw-item-body">\n{frag}\n'
            f'<a class="jw-collapse-bottom" onclick="_jwCollapseItem(this)">'
            f'▲ 收起本条</a>\n</div>\n</details>\n')
def _stage_item_key(stage: str, mid: str, title: str) -> str:
    identity = "\0".join((str(stage or ""), str(mid or ""), _text_of(title)))
    return hashlib.sha256(identity.encode("utf-8", "surrogatepass")).hexdigest()
# 同阶段内「同一语义、不同标题」的条目组。复盘反哺阶段有两条写入链：
# 聚合阶段的 report_type="retro"（标题「反哺进化报告」）与 fupan_done 阶段的
# report_type="fupan"（标题「复盘报告」）。两者标题不同、item_key 也不同，
# 默认会并存，读者无法判断哪份是事实。写入新条目时先移除同组旧条目，
# 保证同一时刻只留最新一份。
_STAGE_ITEM_SEMANTIC_GROUPS: dict[str, tuple[frozenset[str], ...]] = {
    "retro_feedback": (
        frozenset({"反哺进化报告", "复盘报告"}),
    ),
}
def _supersede_item_keys(stage: str, mid: str, title: str) -> tuple[str, ...]:
    """同语义组内被本次写入替代的旧条目键（不含本次标题自身）。"""
    _title = _text_of(title)
    _keys: list[str] = []
    for _group in _STAGE_ITEM_SEMANTIC_GROUPS.get(str(stage or ""), ()):
        if _title not in _group:
            continue
        for _sibling in sorted(_group):
            if _sibling == _title:
                continue
            _keys.append(_stage_item_key(stage, mid, _sibling))
    return tuple(_keys)
def _drop_item_by_key(data: bytes, item_key: str) -> bytes:
    """删除带指定 JW_ITEM_KEY 标记的条目（同 key 全部命中），并重计数。"""
    if not item_key:
        return data
    try:
        doc = data.decode("utf-8")
    except UnicodeDecodeError:
        return data
    marker = f"<!--JW_ITEM_KEY:{item_key}-->"
    _changed = False
    cursor = 0
    while True:
        start = doc.find(_ITEM_OPEN_TAG, cursor)
        if start < 0:
            break
        end = _details_block_end(doc, start)
        if end < 0:
            break
        if marker in doc[start:end]:
            doc = doc[:start] + doc[end:]
            _changed = True
            cursor = start
            continue
        cursor = end
    if not _changed:
        return data
    doc, _count = _recount_items(doc)
    return doc.encode("utf-8")
def _read_stage_doc(path: str) -> str:
    try:
        with open(path, encoding="utf-8") as handle:
            return handle.read()
    except (OSError, UnicodeDecodeError) as exc:
        log_swallowed(__name__, exc, context="stage_doc:read")
        return ""
def _html_item_snapshots(path: str) -> dict[str, dict[str, str]] | None:
    doc = _read_stage_doc(path)
    return _stage_item_snapshots(doc) if doc else None
def _last_count_match(text: str) -> re.Match[str] | None:
    matches = list(_COUNT_RE.finditer(text))
    return matches[-1] if matches else None
def _bump_count(tail: bytes) -> bytes:
    matches = list(_COUNT_BYTES_RE.finditer(tail))
    m = matches[-1] if matches else None
    if m is None:
        return tail
    bumped = str(int(m.group(2)) + 1).encode("ascii")
    return tail[:m.start()] + m.group(1) + bumped + m.group(3) + tail[m.end():]
def _recount_items(doc: str) -> tuple[str, int]:
    count = len(_extract_stage_items(doc, 0))
    m = _last_count_match(doc)
    if m is None:
        return doc, count
    return (doc[:m.start()] + f"{m.group(1)}{count}{m.group(3)}"
            + doc[m.end():], count)
def _quarantine_json_file(json_path: str, skill_dir: str, reason: str) -> str:
    try:
        base = get_backup_base(skill_dir)
    except (OSError, RuntimeError, ValueError) as exc:
        logger.warning("[Stage] %s 隔离目录不可用: %s", reason, exc)
        return ""
    target_dir = os.path.join(base, "orphan_stage_json")
    stem = os.path.splitext(os.path.basename(json_path))[0]
    target = os.path.join(
        target_dir, f"{stem}.{timestamp_ms()}.{uuid.uuid4().hex[:8]}.json")
    try:
        os.makedirs(target_dir, exist_ok=True)
        os.replace(json_path, target)
    except OSError as exc:
        logger.warning("[Stage] %s 隔离失败（保留原文件）: %s: %s",
                       reason, json_path, exc)
        return ""
    logger.warning("[Stage] %s 已隔离: %s -> %s", reason, json_path, target)
    return target
def _restore_quarantined_json(json_path: str, quarantined_path: str) -> None:
    if not quarantined_path or os.path.exists(json_path):
        return
    try:
        os.replace(quarantined_path, json_path)
    except OSError as exc:
        logger.warning("[Stage] 隔离 JSON 恢复失败（备份仍保留）: %s: %s",
                       quarantined_path, exc)
    else:
        logger.info("[Stage] 事务失败，已恢复隔离前文件: %s", json_path)
def _rollback_companion_quarantines(
        quarantines: list[tuple[str, str]]) -> None:
    for json_path, quarantined_path in reversed(quarantines):
        _restore_quarantined_json(json_path, quarantined_path)
def _quarantine_companion_json(path: str, skill_dir: str) -> tuple[str, str]:
    if os.path.isfile(path):
        return "", ""
    try:
        json_path = stage_json_artifact_path(path, skill_dir)
    except (OSError, RuntimeError, ValueError) as exc:
        logger.debug("[Stage] 旧配套 JSON 路径解析失败（跳过隔离）: %s", exc)
        return "", ""
    if not os.path.isfile(json_path):
        return "", ""
    return json_path, _quarantine_json_file(json_path, skill_dir, "旧配套 JSON")
def _create_stage_file(path: str, stage: str, skill_dir: str,
                       round_ts: str, mid: str = _DEFAULT_MID, *,
                       quarantines: list[tuple[str, str]] | None = None) -> bool:
    if stage not in STAGE_META:
        logger.warning("[Stage] 未知阶段 %r（不创建阶段文件）: %s", stage, path)
        return False
    try:
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    except OSError as e:
        logger.warning("[Stage] 阶段文件创建失败(不阻断): %s: %s", path, e)
        return False
    json_path, quarantined = _quarantine_companion_json(path, skill_dir)
    if json_path and not quarantined:
        logger.warning(
            "[Stage] 旧配套 JSON 未能隔离，取消新建阶段文件: %s", path)
        return False
    if not _write_text_soft(
            path, _skeleton(stage, skill_dir, round_ts, mid, html_path=path),
            "阶段文件创建失败"):
        _restore_quarantined_json(json_path, quarantined)
        return False
    if quarantines is not None and quarantined:
        quarantines.append((json_path, quarantined))
    return True
def _atomic_write_bytes(path: str, data: bytes) -> None:
    tmp_path = f"{path}.tmp_{os.getpid()}_{threading.get_ident()}"
    try:
        with open(tmp_path, "wb") as f:
            f.write(data)
        os.replace(tmp_path, path)
    except OSError:
        try:
            discard_tmp_file(tmp_path)
        except OSError as cleanup_err:
            logger.debug("[Stage] 临时文件清理失败: %s: %s", tmp_path, cleanup_err)
        raise
def _read_bytes(path: str) -> bytes | None:
    try:
        with open(path, "rb") as handle:
            return handle.read()
    except OSError as exc:
        log_swallowed(__name__, exc, context="stage_doc:read_bytes")
        return None
def _rollback_html_transaction(path: str, before: bytes | None,
                               existed: bool) -> None:
    if existed:
        if before is None:
            raise OSError("写入前 HTML 内容不可用，无法执行字节级回滚")
        _atomic_write_bytes(path, before)
    elif os.path.isfile(path) and not safe_delete(path):
        raise OSError(f"新建 HTML 回滚未能移入回收站: {path}")
def _replace_keyed_item(data: bytes, item: str, item_key: str) -> bytes | None:
    if not item_key:
        return None
    try:
        doc = data.decode("utf-8")
    except UnicodeDecodeError:
        return None
    marker = f"<!--JW_ITEM_KEY:{item_key}-->"
    cursor = 0
    while True:
        start = doc.find(_ITEM_OPEN_TAG, cursor)
        if start < 0:
            return None
        end = _details_block_end(doc, start)
        if end < 0:
            return None
        if marker in doc[start:end]:
            return (doc[:start] + item + doc[end:]).encode("utf-8")
        cursor = end
def _append_item_in_memory(data: bytes, item: str, *,
                           item_key: str = "",
                           supersede_keys: tuple[str, ...] = ()) -> bytes | None:
    """把单个条目拼进已读入的阶段文件字节流（纯内存，不写盘）。

    返回拼接后的字节；追加锚点缺失时返回 None。单条追加与批量提交共用这
    一份拼接语义，两条路径不会产生不同字节。

    ``supersede_keys`` 列出同语义组内应被本次写入替代的旧条目键，在追加/
    替换前先移除，避免同阶段两份同语义报告并存。
    """
    payload = (_utf8_bytes(item)
               .replace(b"\r\n", b"\n").replace(b"\r", b"\n"))
    if b"\r\n" in data:
        payload = payload.replace(b"\n", b"\r\n")
    for _old_key in supersede_keys or ():
        if _old_key and _old_key != item_key:
            data = _drop_item_by_key(data, _old_key)
    replaced = _replace_keyed_item(data, payload.decode("utf-8"), item_key)
    if replaced is not None:
        return replaced
    pos = data.rfind(_MARK_BYTES)
    if pos < 0:
        return None
    tail = data[pos:]
    if _COUNT_BYTES_RE.search(tail) is None:
        logger.warning("[Stage] 追加时未找到条目计数锚点，计数可能漂移")
    return data[:pos] + payload + _bump_count(tail)


def _append_item_bytes(path: str, item: str, *, item_key: str = "",
                       supersede_keys: tuple[str, ...] = ()) -> bool:
    try:
        with open(path, "rb") as f:
            data = f.read()
        new_data = _append_item_in_memory(
            data, item, item_key=item_key, supersede_keys=supersede_keys)
        if new_data is None:
            logger.warning("[Stage] 追加锚点缺失(非阶段文件?): %s", path)
            return False
        _atomic_write_bytes(path, new_data)
        return True
    except OSError as e:
        logger.warning("[Stage] 条目追加失败(不阻断): %s: %s", path, e)
        return False
def _new_stage_json(stage: str, skill_dir: str, round_ts: str,
                    html_path: str, json_path: str) -> dict:
    return {
        "schema_version": "jwsgj.stage-report/v1",
        "stage": stage,
        "skill_dir": _norm_sd(skill_dir),
        "round_start_ts": round_ts,
        "html_file": os.path.basename(html_path),
        "json_file": os.path.basename(json_path),
        "updated_at": timestamp_ms(),
        "item_count": 0,
        "items": {},
    }
def _json_key(value) -> str:
    if isinstance(value, str):
        return value
    if value is None:
        return "null"
    if isinstance(value, bool):
        return "true" if value else "false"
    return str(value)
def _json_payload(value, _depth: int = 0) -> object:
    if _depth > 32:
        return str(value)
    if isinstance(value, float) and not math.isfinite(value):
        return "NaN" if math.isnan(value) else (
            "Infinity" if value > 0 else "-Infinity")
    if isinstance(value, Iterator):
        return [_json_payload(item, _depth + 1) for item in value]
    if isinstance(value, dict):
        return {_json_key(key): _json_payload(item, _depth + 1)
                for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [_json_payload(item, _depth + 1) for item in value]
    if isinstance(value, (set, frozenset)):
        return sorted((_json_payload(item, _depth + 1) for item in value),
                      key=str)
    return value
_STAGE_JSON_CACHE_MAX = 16
_STAGE_JSON_READ_CACHE: dict[str, tuple[tuple[int, int], dict]] = {}
_STAGE_JSON_READ_LOCK = threading.Lock()
def _stage_json_fingerprint(json_path: str) -> tuple[int, int] | None:
    """返回配套 JSON 的文件指纹；文件不可 stat 时返回 None。"""
    try:
        info = os.stat(json_path)
    except OSError:
        return None
    return (info.st_mtime_ns, info.st_size)
def _stage_json_cached(json_path: str) -> dict | None:
    """返回该路径**已规范化**的配套 JSON 文档，指纹不符则返回 None。

    同一轮报告发射会对同一个阶段文件反复追加条目：实测 91 次调用只落在
    11 个路径上（去重率 87.9%，单文件最高 75 次），原实现每次都把整份
    文档 ``json.load`` 后再 ``_json_payload`` 深度规范化，成本随条目数呈
    二次增长（实测 9.15 s）。文档仅由本模块写盘，故写盘后立即以新指纹
    回填缓存，读取侧按 ``(mtime_ns, size)`` 命中，语义与逐次解析等价。
    """
    fingerprint = _stage_json_fingerprint(json_path)
    if fingerprint is None:
        return None
    with _STAGE_JSON_READ_LOCK:
        cached = _STAGE_JSON_READ_CACHE.get(json_path)
    if cached is not None and cached[0] == fingerprint:
        return cached[1]
    return None
def _stage_json_store(json_path: str, doc: dict) -> None:
    """写盘后以新指纹回填规范化文档，供同轮后续追加直接命中。"""
    fingerprint = _stage_json_fingerprint(json_path)
    if fingerprint is None:
        return
    with _STAGE_JSON_READ_LOCK:
        if len(_STAGE_JSON_READ_CACHE) >= _STAGE_JSON_CACHE_MAX:
            _STAGE_JSON_READ_CACHE.clear()
        _STAGE_JSON_READ_CACHE[json_path] = (fingerprint, doc)
def _stage_json_drop(json_path: str) -> None:
    """隔离/回滚后丢弃缓存，避免指向已不存在的旧文档。"""
    with _STAGE_JSON_READ_LOCK:
        _STAGE_JSON_READ_CACHE.pop(json_path, None)
def _load_stage_json_doc(json_path: str, stage: str, skill_dir: str,
                         round_ts: str, path: str) -> tuple[dict, str]:
    """读取（或新建）配套 JSON 文档。

    返回 ``(doc, quarantined_path)``；``quarantined_path`` 非空表示原文件
    因损坏/结构非法被隔离，调用方在后续写盘失败时需要把它恢复。
    """
    cached_doc = _stage_json_cached(json_path)
    if cached_doc is not None:
        # 浅拷贝顶层：调用方只替换 `items` 容器与顶层字段，条目字典只读。
        return dict(cached_doc), ""
    if not os.path.isfile(json_path):
        return _new_stage_json(
            stage, skill_dir, round_ts, path, json_path), ""
    loaded: object = None
    read_ok = False
    try:
        with open(json_path, encoding="utf-8-sig") as handle:
            loaded = json.load(handle)
        read_ok = True
    except (OSError, ValueError, RecursionError) as exc:
        logger.warning(
            "[Stage] 配套 JSON 读取失败(%s)，隔离后重建: %s: %s",
            type(exc).__name__, json_path, exc)
        quarantined = _quarantine_json_file(
            json_path, skill_dir, "损坏的配套 JSON")
        _stage_json_drop(json_path)
        if not quarantined:
            raise
        return _new_stage_json(
            stage, skill_dir, round_ts, path, json_path), quarantined
    if read_ok:
        if (not isinstance(loaded, dict)
                or not isinstance(loaded.get("items"), dict)
                or any(not isinstance(item, dict)
                       for item in loaded["items"].values())):
            logger.warning(
                "[Stage] 配套 JSON 结构非法，隔离后重建: %s", json_path)
            quarantined = _quarantine_json_file(
                json_path, skill_dir, "结构非法的配套 JSON")
            _stage_json_drop(json_path)
            if not quarantined:
                raise ValueError("配套 JSON 结构非法且隔离失败: %s" % (json_path,))
            return _new_stage_json(
                stage, skill_dir, round_ts, path, json_path), quarantined
        return _json_payload(loaded), ""
    return _new_stage_json(stage, skill_dir, round_ts, path, json_path), ""


def _reconcile_stage_json_items(
        items: dict, html_items: dict[str, dict[str, str]], *,
        current_key: str = "") -> dict:
    """按最终 HTML 顺序对账 JSON 条目，并为 HTML-only 条目保留缺失标记。"""
    keep = set(html_items)
    if current_key:
        keep.add(current_key)
    filtered = {key: value for key, value in items.items() if key in keep}
    ordered: dict[str, dict] = {}
    for key, meta in html_items.items():
        if key in filtered:
            ordered[key] = filtered[key]
            continue
        ordered[key] = {
            "title": str(meta.get("title") or key[:8]),
            "mid": "",
            "report_type": "",
            "icon": str(meta.get("icon") or _DEFAULT_ITEM_ICON),
            "updated_at": timestamp_ms(),
            "payload": None,
            "payload_missing": True,
            "source": "html_only",
        }
    if current_key and current_key not in ordered:
        ordered = {current_key: filtered[current_key], **ordered}
    return ordered


#: 阶段配套 JSON 单个列表载荷的保留条数上限。
#:
#: 历史缺陷：方法 A 的 ``profiles``（307 份 × ≈41KB 五维画像）被原样写进
#: ``payload.payload.sub_results``，而 ``sub_results`` / ``detector_results`` /
#: ``payload`` 又是同一对象的多个别名；``json.dumps`` 不做引用去重，单阶段
#: JSON 实测 150.7 MB（6 条发现）。阶段报告是给人看的留痕，不是全量数据仓，
#: 超限部分按「保留前 N 条 + 记录原始条数」压缩。
_STAGE_PAYLOAD_LIST_CAP = 50

#: 递归压缩的最大深度（防畸形载荷无限下探）。
_STAGE_PAYLOAD_MAX_DEPTH = 12


def _cap_stage_payload(value: Any, depth: int = 0) -> Any:
    """递归压缩阶段载荷里超长的列表（保留前 N 条并记录原始条数）。"""
    if depth >= _STAGE_PAYLOAD_MAX_DEPTH:
        return value
    if isinstance(value, dict):
        return {k: _cap_stage_payload(v, depth + 1) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        capped = [_cap_stage_payload(item, depth + 1)
                  for item in value[:_STAGE_PAYLOAD_LIST_CAP]]
        if len(value) > _STAGE_PAYLOAD_LIST_CAP:
            capped.append({
                "_truncated": True,
                "kept": _STAGE_PAYLOAD_LIST_CAP,
                "total": len(value),
                "_note": "阶段报告按上限保留前 N 条，完整数据见对应诊断方法的中间产物",
            })
        return capped
    if isinstance(value, (set, frozenset)):
        return _cap_stage_payload(sorted(value, key=repr), depth + 1)
    return value


def _merge_stage_json_doc(doc: dict, *, stage: str, skill_dir: str,
                          round_ts: str, path: str, json_path: str,
                          title: str, mid: str, icon: str, item_key: str,
                          payload, report_type: str = "",
                          html_items: dict[str, dict[str, str]] | None = None
                          ) -> dict:
    """把一个条目合并进配套 JSON 文档（纯内存，不写盘）。"""
    items = dict(doc.get("items") or {})
    items[item_key] = {
        "title": _text_of(title),
        "mid": str(mid or ""),
        "report_type": str(report_type or ""),
        "icon": _text_of(icon),
        "updated_at": timestamp_ms(),
        "payload": ({} if payload is None
                    else _cap_stage_payload(_json_payload(payload))),
    }
    if html_items is not None:
        items = _reconcile_stage_json_items(
            items, html_items, current_key=item_key)
    doc.update({
        "stage": stage,
        "skill_dir": _norm_sd(skill_dir),
        "round_start_ts": round_ts,
        "html_file": os.path.basename(path),
        "json_file": os.path.basename(json_path),
        "updated_at": timestamp_ms(),
        "item_count": len(items),
        "items": items,
    })
    return doc


def _write_stage_json_doc(json_path: str, doc: dict) -> None:
    """把配套 JSON 文档整体序列化并原子写盘（一次 dumps）。"""
    os.makedirs(os.path.dirname(json_path) or ".", exist_ok=True)
    blob = _utf8_bytes(
        json.dumps(doc, ensure_ascii=False, indent=2, default=str,
                   allow_nan=False))
    _atomic_write_bytes(json_path, blob)
    _stage_json_store(json_path, doc)


def _sync_stage_json(path: str, title: str, *, skill_dir: str,
                     round_ts: str, mid: str, stage: str, icon: str,
                     item_key: str, payload, report_type: str = "",
                     html_items: dict[str, dict[str, str]] | None = None) -> str:
    stage = stage or stage_of_file(path)
    quarantined_json = ""
    try:
        json_path = stage_json_artifact_path(path, skill_dir)
        doc, quarantined_json = _load_stage_json_doc(
            json_path, stage, skill_dir, round_ts, path)
        doc = _merge_stage_json_doc(
            doc, stage=stage, skill_dir=skill_dir, round_ts=round_ts,
            path=path, json_path=json_path, title=title, mid=mid, icon=icon,
            item_key=item_key, payload=payload, report_type=report_type,
            html_items=html_items)
        _write_stage_json_doc(json_path, doc)
        return json_path
    except (OSError, RuntimeError, TypeError, ValueError, RecursionError) as exc:
        logger.warning("[Stage] 配套 JSON 写入失败: %s: %s", path, exc)
        if quarantined_json:
            _restore_quarantined_json(json_path, quarantined_json)
            _stage_json_drop(json_path)
        return ""
    except Exception as exc:
        logger.warning("[Stage] 配套 JSON 归一异常，交由调用方回滚: %s: %s",
                       path, exc)
        if quarantined_json:
            _restore_quarantined_json(json_path, quarantined_json)
            _stage_json_drop(json_path)
        return ""
@dataclass(frozen=True)
class _PendingSection:
    """批量提交队列中的一条阶段条目（尚未落盘）。"""

    title: str
    rendered_html: str
    icon: str
    skill_dir: str
    round_ts: str
    mid: str
    stage: str
    payload: object
    report_type: str
    sync_json: bool


_STAGE_BATCH_LOCAL = threading.local()

def _stage_batch_queue() -> dict[str, list[_PendingSection]]:
    queue = getattr(_STAGE_BATCH_LOCAL, "queue", None)
    if queue is None:
        queue = {}
        _STAGE_BATCH_LOCAL.queue = queue
    return queue


def _stage_batch_active() -> bool:
    """当前线程是否处于阶段报告批次内（批次内追加只入队，不落盘）。"""
    return getattr(_STAGE_BATCH_LOCAL, "depth", 0) > 0


@contextmanager
def stage_report_batch() -> Iterator[None]:
    """把同一批次内的阶段追加合并为「一次读 + 一次写」。

    逐项追加的实现是「读整份 HTML → 拼接 → 原子写回」再「读整份 JSON →
    合并 → 全量序列化写回」，成本随条目数呈二次增长：实测 71 个治疗项
    触发 90 次追加、12.7s 全量序列化。批次内改为内存累积、退出时一次
    提交，产物字节与逐项追加一致；提交失败整批回滚，不留半成品。
    """
    previous_depth = getattr(_STAGE_BATCH_LOCAL, "depth", 0)
    _STAGE_BATCH_LOCAL.depth = previous_depth + 1
    try:
        yield
    finally:
        _STAGE_BATCH_LOCAL.depth = previous_depth
        if previous_depth == 0:
            _flush_stage_batch()


def _enqueue_stage_section(path: str, title: str, rendered_html: str,
                           icon: str, *, skill_dir: str, round_ts: str,
                           mid: str, stage: str, payload, report_type: str,
                           sync_json: bool) -> None:
    _stage_batch_queue().setdefault(path, []).append(_PendingSection(
        title=title, rendered_html=rendered_html, icon=icon,
        skill_dir=skill_dir, round_ts=round_ts, mid=mid, stage=stage,
        payload=payload, report_type=report_type, sync_json=sync_json))


def _flush_stage_batch() -> None:
    queue = _stage_batch_queue()
    _STAGE_BATCH_LOCAL.queue = {}
    for path, sections in queue.items():
        _commit_stage_sections(path, sections)


def _commit_stage_sections(path: str, sections: list[_PendingSection]) -> None:
    """整批提交同一个阶段文件的所有条目；失败只告警，不阻断治理流程。"""
    if not sections:
        return
    lock_stage = stage_of_file(path) or sections[0].stage
    _locked_emit(
        os.path.dirname(path) or ".", f"htmlstage_{lock_stage or 'batch'}", path,
        "批量提交失败", "批量提交锁竞争放弃",
        lambda: _commit_stage_sections_locked(path, sections))


def _commit_stage_sections_locked(path: str, sections: list[_PendingSection]) -> None:
    first = sections[0]
    file_stage = stage_of_file(path)
    stage = file_stage or first.stage
    first_context = (normalize_skill_key(first.skill_dir), first.round_ts)
    for section in sections:
        context = (normalize_skill_key(section.skill_dir), section.round_ts)
        if context != first_context:
            logger.warning(
                "[Stage] 批量条目 owner/round 不一致，拒绝整批写入: %s", path)
            return
        if not _check_stage_owner(path, section.skill_dir, section.round_ts):
            return
    if not ensure_stage_file(
            path, stage, first.skill_dir, first.round_ts, first.mid):
        return
    file_round = (_file_round(_read_head(path)) or _filename_round(path)
                  or first.round_ts)
    before = _read_bytes(path)
    if before is None:
        raise OSError("阶段文件读取失败: %s" % (path,))
    data = before
    for section in sections:
        item_key = _stage_item_key(stage, section.mid, section.title)
        _supersede = _supersede_item_keys(
            stage, section.mid, section.title)
        item = _wrap_item(section.title, extract_fragment(section.rendered_html),
                          section.icon, item_key=item_key)
        new_data = _append_item_in_memory(
            data, item, item_key=item_key, supersede_keys=_supersede)
        if new_data is None:
            raise RuntimeError("阶段文件追加锚点缺失: %s" % (path,))
        data = new_data
    _atomic_write_bytes(path, data)
    if not any(section.sync_json for section in sections):
        return
    json_path = ""
    quarantined = ""
    try:
        json_path = stage_json_artifact_path(path, first.skill_dir)
        doc, quarantined = _load_stage_json_doc(
            json_path, stage, first.skill_dir, file_round, path)
        for section in sections:
            if not section.sync_json:
                continue
            doc = _merge_stage_json_doc(
                doc, stage=stage, skill_dir=first.skill_dir,
                round_ts=file_round, path=path, json_path=json_path,
                title=section.title, mid=section.mid, icon=section.icon,
                item_key=_stage_item_key(stage, section.mid, section.title),
                payload=section.payload, report_type=section.report_type)
        # 单写与批写共用同一份 HTML/JSON 对账：既裁剪被替代条目，
        # 也为 JSON 缺失/损坏前已存在的 HTML-only 条目补上 payload_missing。
        _snapshots = _html_item_snapshots(path)
        if _snapshots is not None:
            doc["items"] = _reconcile_stage_json_items(
                dict(doc.get("items") or {}), _snapshots)
            doc["item_count"] = len(doc["items"])
        _write_stage_json_doc(json_path, doc)
    # 任意归一/序列化异常都必须回滚，随后继续交给外层记录并重抛。
    except Exception:
        try:
            _atomic_write_bytes(path, before)
        except OSError as rollback_exc:
            logger.warning("[Stage] 批量提交回滚 HTML 失败: %s: %s",
                           path, rollback_exc)
        if quarantined:
            _restore_quarantined_json(json_path, quarantined)
            _stage_json_drop(json_path)
        raise


def _check_stage_owner(path: str, skill_dir: str, round_ts: str) -> bool:
    """校验追加上下文与现有阶段文件的 owner/轮次一致；冲突时拒绝写入。"""
    if not (os.path.exists(path) and os.path.isfile(path)):
        return True
    head = _read_head(path)
    owner = normalize_skill_key(_meta_of(head).get("skill") or "")
    target = normalize_skill_key(skill_dir)
    file_round = _file_round(head) or _filename_round(path)
    if (target != owner
            or (round_ts and file_round and round_ts != file_round)):
        logger.warning(
            "[Stage] 追加上下文与现有文件冲突（owner=%s/%s, round=%s/%s），"
            "拒绝写入: %s", owner or "-", target or "-",
            file_round or "-", round_ts or "-", path)
        return False
    return True


def append_stage_section(path: str, title: str, rendered_html: str,
                         icon: str = _DEFAULT_ITEM_ICON, *,
                         skill_dir: str = _DEFAULT_SKILL_DIR, round_ts: str = _DEFAULT_ROUND_TS,
                         mid: str = _DEFAULT_MID, stage: str = "", payload=None,
                         report_type: str = "", sync_json: bool = False) -> bool:
    path = _path_arg(path)
    if not path:
        logger.warning("[Stage] 阶段条目追加缺少文件路径（跳过）")
        return False
    if _stage_batch_active():
        _enqueue_stage_section(
            path, title, rendered_html, icon, skill_dir=skill_dir,
            round_ts=round_ts, mid=mid, stage=stage, payload=payload,
            report_type=report_type, sync_json=sync_json)
        return True
    file_stage = stage_of_file(path)
    if stage and file_stage and stage != file_stage:
        logger.warning("[Stage] 阶段参数 %r 与文件名阶段 %r 不一致，按文件名归口: %s",
                       stage, file_stage, path)
        stage = file_stage
    existed_before = os.path.exists(path)
    if not _check_stage_owner(path, skill_dir, round_ts):
        return False
    quarantines: list[tuple[str, str]] = []
    if not ensure_stage_file(
            path, stage, skill_dir, round_ts, mid, _quarantines=quarantines):
        return False
    before = _read_bytes(path) if existed_before else None
    file_round = (_file_round(_read_head(path)) or _filename_round(path)
                  or round_ts)
    _file_stage = stage or stage_of_file(path)
    item_key = _stage_item_key(_file_stage, mid, title)
    # 同语义组的旧条目（如「反哺进化报告」与「复盘报告」）先移除，
    # 保证同阶段只留最新一份事实。
    _supersede = _supersede_item_keys(_file_stage, mid, title)
    item = _wrap_item(title, extract_fragment(rendered_html), icon,
                      item_key=item_key)
    if not _append_item_bytes(path, item, item_key=item_key,
                              supersede_keys=_supersede):
        try:
            _rollback_html_transaction(path, before, existed_before)
        except OSError as exc:
            logger.warning("[Stage] 条目追加失败且 HTML 撤销失败: %s: %s",
                           path, exc)
        else:
            _rollback_companion_quarantines(quarantines)
        return False
    if sync_json:
        json_path = _sync_stage_json(
            path, title, skill_dir=skill_dir, round_ts=file_round, mid=mid,
            stage=stage or stage_of_file(path), icon=icon, item_key=item_key,
            payload=payload, report_type=report_type,
            html_items=_html_item_snapshots(path))
        if json_path:
            return True
        try:
            _rollback_html_transaction(path, before, existed_before)
        except OSError as exc:
            logger.warning("[Stage] 配套 JSON 写入失败且 HTML 回滚失败: %s: %s",
                           path, exc)
        else:
            _rollback_companion_quarantines(quarantines)
            logger.warning(
                "[Stage] 配套 JSON 写入失败，已%s: %s",
                "回滚 HTML 追加" if existed_before else "删除新建阶段文件",
                path)
        return False
    return True
def _splice_final_block(path: str, inner_html: str) -> bool:
    path = _path_arg(path)
    if not path:
        logger.warning("[Stage] 汇总块替换缺少文件路径（跳过）")
        return False
    data = _read_bytes(path)
    if data is None:
        return False
    newline = _newline_of(data)
    try:
        doc = data.decode("utf-8")
    except UnicodeDecodeError as _decode_e:
        logger.warning("[Stage] 最终报告非 UTF-8，保留原文件并跳过汇总替换: %s: %s",
                       path, _decode_e)
        return False
    a_idx = doc.find(_FINAL_ANCHOR)
    e_idx = doc.find(_FINAL_BLOCK_END)
    if a_idx < 0 or e_idx < 0 or a_idx > e_idx:
        logger.warning("[Stage] 最终报告缺少汇总块锚点，跳过替换: %s", path)
        return False
    start = a_idx + len(_FINAL_ANCHOR)
    new_doc, _count = _recount_items(
        doc[:start] + "\n" + inner_html + doc[e_idx:])
    logger.debug("[Stage] 汇总块重写: 条目=%d: %s", _count, path)
    return _write_text_soft(path, new_doc, "汇总块替换失败", newline=newline)
def _final_summary_fragment(items: list[tuple[str, str, str]]) -> str:
    sections = []
    for title, rendered, icon in items:
        fragment = _namespace_fragment_ids(
            extract_fragment(rendered), f"jwi{uuid.uuid4().hex[:8]}")
        heading = (f"{_html.escape(_text_of(icon) or '🏁')} "
                   f"{_html.escape(_text_of(title))}")
        sections.append(
            f'<section class="jw-final-part"><h2>{heading}</h2>'
            f"{fragment}</section>")
    return "".join(sections)
def replace_final_block_multi(path: str, items: list[tuple[str, str, str]]) -> bool:
    items = list(items)
    if not items:
        return _splice_final_block(path, "")
    title = STAGE_META["final"]["title"]
    inner = _wrap_item(
        title, _final_summary_fragment(items), "🏁",
        item_key=_stage_item_key("final", "", title), namespace_ids=False)
    return _splice_final_block(path, inner)
def _locked_emit(skill_dir: str, lock_name: str, path: str,
                 op_fail: str, op_giveup: str, action) -> str:
    for attempt in range(3):
        try:
            with ProcessLock(skill_dir or ".", lock_name):
                return action()
        except ConcurrentExecutionError as _swallow_e:
            log_swallowed(__name__, _swallow_e, context='_locked_emit:ConcurrentExecutionError')
            if attempt < 2:
                time.sleep(0.05)
            continue
        except Exception as _aee:
            logger.warning("[Stage] %s(不阻断): %s", op_fail, _aee)
            return ""
    logger.warning("[Stage] %s(不阻断): %s", op_giveup, path)
    return ""
def _resolve_emit_context(stage: str, skill_dir: str, mid: str,
                          ) -> tuple[str, str, str] | None:
    _label = "最终报告" if stage == "final" else "阶段文件"
    skill_dir = _norm_sd(skill_dir)
    if not skill_dir:
        logger.warning("[Stage] 缺少技能归属（空 skill_dir），抑制%s发射", _label)
        return None
    try:
        _hb = get_html_report_base()
    except Exception as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_resolve_emit_context:Exc')
        _hb = ""
    if _is_sandbox_skill_anchor(skill_dir, _hb):
        logger.info("[Stage] 沙箱跨边界锚抑制%s发射: %s", _label, skill_dir)
        return None
    try:
        round_ts = _round_ts(skill_dir)
        path = resolve_stage_file(stage, skill_dir, mid, round_ts=round_ts)
        file_round = _file_round(_read_head(path)) or _filename_round(path)
        round_ts = file_round or _resolve_round_token(round_ts)
    except Exception as _rse:
        logger.warning("[Stage] %s解析失败(不发射): %s", _label, _rse)
        return None
    if not str(path).lower().endswith(".html"):
        logger.error("[Stage] %s落点非 .html（htm 只存 html 契约）: %s",
                     _label, path)
        return None
    return skill_dir, path, round_ts
def _stage_file_compatible(head: str, skill_dir: str, round_ts: str,
                           path: str = "") -> bool:
    file_round = _file_round(head) or _filename_round(path)
    if round_ts and file_round and round_ts != file_round:
        return False
    return _file_skill_ok(head, skill_dir)
def _mtime_of(path: str) -> float:
    try:
        return os.path.getmtime(path)
    except OSError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_mtime_of:OSError')
        return 0.0
def _pick_stage_candidate(pattern: str, skill_dir: str, round_ts: str) -> str | None:
    candidates = sorted(glob.glob(pattern), key=os.path.basename)
    candidates.sort(key=_mtime_of, reverse=True)
    for cand in candidates:
        if re.search(r"\d{17}$", os.path.splitext(os.path.basename(cand))[0]) is None:
            continue
        if _stage_file_compatible(
                _read_head(cand), skill_dir, round_ts, path=cand):
            return cand
    return None
def _stage_owner_token(skill_dir: str) -> str:
    seed = normalize_skill_key(skill_dir) or "anonymous"
    return uuid.uuid5(uuid.NAMESPACE_URL, seed).hex[:8]
def _fresh_stage_path(base: str, stage: str, skill_dir: str,
                      round_ts: str, mid: str) -> str:
    base_ts = _resolve_round_token(round_ts)
    primary = os.path.join(base, stage_filename(stage, base_ts, mid))
    if not os.path.isfile(primary):
        return primary
    if _stage_file_compatible(
            _read_head(primary), skill_dir, base_ts, path=primary):
        return primary
    token = _stage_owner_token(skill_dir)
    owned = os.path.join(
        base, stage_filename(stage, base_ts, mid, owner=token))
    if not os.path.isfile(owned):
        return owned
    if _stage_file_compatible(
            _read_head(owned), skill_dir, base_ts, path=owned):
        return owned
    for _ in range(3):
        unique = os.path.join(
            base, stage_filename(
                stage, base_ts, mid, owner=uuid.uuid4().hex[:8]))
        if not os.path.isfile(unique):
            return unique
    return os.path.join(
        base, stage_filename(stage, base_ts, mid, owner=uuid.uuid4().hex))
def _resolve_stage_path(base: str, stage: str, skill_dir: str,
                        round_ts: str, mid: str) -> str:
    pattern = os.path.join(
        glob.escape(base), stage_filename(stage, "", mid, wildcard=True))
    picked = _pick_stage_candidate(pattern, skill_dir, round_ts)
    return picked or _fresh_stage_path(base, stage, skill_dir, round_ts, mid)
def resolve_stage_file(stage: str, skill_dir: str, mid: str = _DEFAULT_MID,
                       *, round_ts: str | None = None) -> str:
    skill_dir = _norm_sd(skill_dir)
    if not skill_dir:
        raise ValueError("resolve_stage_file 需要非空 skill_dir（阶段报告必须归属技能）")
    base = get_html_report_base()
    if round_ts is None:
        round_ts = _round_ts(skill_dir)
    return _resolve_stage_path(
        base, stage, skill_dir, round_ts, "" if stage == "final" else mid)
def ensure_stage_file(path: str, stage: str = "", skill_dir: str = _DEFAULT_SKILL_DIR,
                      round_ts: str = _DEFAULT_ROUND_TS, mid: str = _DEFAULT_MID, *,
                      _quarantines: list[tuple[str, str]] | None = None) -> bool:
    path = _path_arg(path)
    if not path:
        logger.warning("[Stage] 追加前准备缺少文件路径（跳过）")
        return False
    if os.path.isfile(path):
        if not upgrade_stage_skeleton(path, skill_dir, round_ts, mid):
            logger.warning("[Stage] 旧骨架升级失败，按原文件续写(不阻断): %s", path)
        return True
    resolved = stage or stage_of_file(path)
    if not resolved:
        logger.warning("[Stage] 文件不存在且无法确定阶段（不创建）: %s", path)
        return False
    return _create_stage_file(
        path, resolved, skill_dir, round_ts, mid, quarantines=_quarantines)
def _emit_locked(stage: str, skill_dir: str, mid: str, writer,
                 *, fail: str, giveup: str) -> str:
    ctx = _resolve_emit_context(stage, skill_dir, mid)
    if ctx is None:
        return ""
    skill_dir, path, round_ts = ctx
    quarantines: list[tuple[str, str]] = []
    def _cleanup_failed_creation(path_existed: bool) -> None:
        if path_existed:
            return
        try:
            _rollback_html_transaction(path, None, False)
        except OSError as exc:
            logger.warning("[Stage] 发射失败且新建 HTML 撤销失败: %s: %s", path, exc)
        else:
            _rollback_companion_quarantines(quarantines)
    def _act():
        nonlocal path
        path_existed = os.path.isfile(path)
        if path_existed and not _stage_file_compatible(
                _read_head(path), skill_dir, round_ts, path=path):
            logger.info("[Stage] 锁等待期间候选归属或轮次变化，改选隔离路径: %s", path)
            path = _fresh_stage_path(
                os.path.dirname(path), stage, skill_dir, round_ts, mid)
            path_existed = os.path.isfile(path)
        try:
            if not ensure_stage_file(
                    path, stage, skill_dir, round_ts, mid,
                    _quarantines=quarantines):
                _cleanup_failed_creation(path_existed)
                return ""
            if writer(path, skill_dir, round_ts):
                return path
        except Exception:
            _cleanup_failed_creation(path_existed)
            raise
        _cleanup_failed_creation(path_existed)
        return ""
    # Different skills can resolve the same shared report path. Scope the lock
    # to that path's directory so their independent skill namespaces cannot
    # both claim the file and roll back each other's newly created report.
    return _locked_emit(os.path.dirname(path), f"htmlstage_{stage}", path,
                        fail, giveup, _act)
def emit_final_block(skill_dir: str,
                     items: list[tuple[str, str, str]], *, payload=None) -> str:
    items = list(items)
    if not items:
        logger.warning("[Stage] 最终汇总块为空，跳过发射: %s", skill_dir)
        return ""
    def _writer(path: str, sd: str, rt: str) -> bool:
        before = _read_bytes(path)
        if not replace_final_block_multi(path, items):
            return False
        title = STAGE_META["final"]["title"]
        snapshots = _html_item_snapshots(path)
        if snapshots is None:
            logger.warning("[Stage] 最终报告条目快照读取失败，JSON 保留合并口径: %s",
                           path)
        json_path = _sync_stage_json(
            path, title, skill_dir=sd, round_ts=rt, mid="", stage="final",
            icon="🏁", item_key=_stage_item_key("final", "", title),
            payload=payload if payload is not None else {
                "sections": [item[0] for item in items]},
            report_type="final", html_items=snapshots)
        if json_path:
            return True
        if before is not None:
            try:
                _atomic_write_bytes(path, before)
                logger.warning("[Stage] 最终报告 JSON 写入失败，已回滚 HTML 汇总块: %s",
                               path)
            except OSError as exc:
                logger.warning("[Stage] 最终报告 JSON 写入失败且 HTML 回滚失败: %s: %s",
                               path, exc)
        else:
            logger.warning("[Stage] 最终报告 JSON 写入失败且无回滚基线"
                           "（汇总块保留）: %s", path)
        return False
    return _emit_locked(
        "final", skill_dir, "", _writer,
        fail="汇总块发射失败", giveup="最终报告锁竞争放弃块替换")
def emit_to_stage(stage: str, skill_dir: str, title: str,
                  rendered_html: str, mid: str = _DEFAULT_MID,
                  icon: str = "", *, payload=None, report_type: str = "") -> str:
    if stage not in STAGE_META:
        logger.warning("[Stage] 未知阶段 %r(不发射): %s", stage, title)
        return ""
    return _emit_locked(
        stage, skill_dir, mid,
        lambda path, sd, rt: append_stage_section(
            path, title, rendered_html, icon or STAGE_META[stage]["icon"],
            skill_dir=sd, round_ts=rt, mid=mid, stage=stage, payload=payload,
            report_type=report_type, sync_json=True),
        fail="阶段追加失败", giveup="阶段锁竞争放弃追加")

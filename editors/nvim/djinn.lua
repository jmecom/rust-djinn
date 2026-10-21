-- Djinn demo config for Neovim 0.10+ (no plugins).
--   nvim -u editors/nvim/djinn.lua example/clamp/src/spec.rs
--
-- rust-analyzer handles the Rust; rust-djinn-lsp adds, for the crate's spec
-- file: a status line drawn BELOW every func/rel (virtual lines built from
-- the server's code lenses), smoke-test diagnostics as you type, progress
-- reports for implement/verify, and jumps to the
-- obligations. Keys (leader = space):
--   <leader>di  implement (agent)   <leader>dv  verify     <leader>ds  smoke-test
--   <leader>do  open obligations    <leader>dp  open proofs <leader>dg  guide
--   <leader>dS  status              <leader>dl  run a code lens on this line
--   gl          show the diagnostic under the cursor

-- the server: on PATH (symlinked into ~/.cargo/bin), else the debug build
local DJINN_LSP = vim.fn.exepath("rust-djinn-lsp")
if DJINN_LSP == "" then DJINN_LSP = vim.fn.expand("~/.cargo/bin/rust-djinn-lsp") end
if vim.fn.executable(DJINN_LSP) == 0 then
  local config_file = debug.getinfo(1, "S").source:sub(2)
  local checkout = vim.fn.fnamemodify(config_file, ":p:h:h:h")
  DJINN_LSP = checkout .. "/rust-djinn/target/debug/rust-djinn-lsp"
end
local AGENT = "codex" -- or "claude"
-- The status is drawn on its own line below each function (virtual lines).
-- The server also offers it as an inline inlay hint for editors that cannot
-- do that; showing both here would duplicate it, so it is off by default.
local INLINE_HINTS = false

vim.g.mapleader = " "
vim.o.number = true
vim.o.signcolumn = "yes"
vim.o.updatetime = 400
vim.o.termguicolors = true

-- ------------------------------------------------------------ diagnostics
vim.diagnostic.config({
  virtual_text = { source = "if_many", spacing = 2, prefix = "■" },
  severity_sort = true,
  float = { border = "rounded", source = true },
})
vim.keymap.set("n", "gl", vim.diagnostic.open_float, { desc = "diagnostic under cursor" })
vim.api.nvim_set_hl(0, "DjinnStatus", { fg = "#8a8f98", italic = true })
vim.api.nvim_set_hl(0, "DjinnStatusOk", { fg = "#6fbf73", italic = true })
vim.api.nvim_set_hl(0, "DjinnStatusBad", { fg = "#e06c75", italic = true })

-- ------------------------------------------------------ status under fns
-- The server's code lenses carry the status (`djinn: …`) plus buttons.
-- Draw the status lens as a virtual line under the `fn` line.
local ns = vim.api.nvim_create_namespace("djinn-status")

local function djinn_client(bufnr)
  return vim.lsp.get_clients({ bufnr = bufnr, name = "rust-djinn-lsp" })[1]
end

-- Neovim 0.11 made `client.request` a method (`client:request`); 0.10 has only the function.
local function lsp_request(client, method, params, handler, bufnr)
  if vim.fn.has("nvim-0.11") == 1 then
    return client:request(method, params, handler, bufnr)
  end
  return client.request(method, params, handler, bufnr)
end

local function draw_status(bufnr)
  local client = djinn_client(bufnr)
  if not client then return end
  local params = { textDocument = vim.lsp.util.make_text_document_params(bufnr) }
  lsp_request(client, "textDocument/codeLens", params, function(err, lenses)
    if err or not lenses or not vim.api.nvim_buf_is_valid(bufnr) then return end
    vim.api.nvim_buf_clear_namespace(bufnr, ns, 0, -1)
    local by_line = {}
    for _, lens in ipairs(lenses) do
      local t = lens.command and lens.command.title or ""
      if t:match("^djinn: ") then
        local line = lens.range.start.line
        by_line[line] = by_line[line] or {}
        table.insert(by_line[line], (t:gsub("^djinn: ", "")))
      end
    end
    for line, parts in pairs(by_line) do
      local text = table.concat(parts, " · ")
      local hl = text:find("✓ ok") and "DjinnStatusOk"
        or (text:find("smoke:") and "DjinnStatusBad" or "DjinnStatus")
      local indent = (vim.api.nvim_buf_get_lines(bufnr, line, line + 1, false)[1] or ""):match("^%s*") or ""
      vim.api.nvim_buf_set_extmark(bufnr, ns, line, 0, {
        virt_lines = { { { indent .. "    ⤷ " .. text, hl } } },
        virt_lines_above = false,
      })
    end
  end, bufnr)
end

-- redraw when the server asks for a lens refresh (after verify/implement/lint);
-- registered per client below, and also on a slow timer as a safety net so
-- the line under the function can never stay stale.
local function on_lens_refresh(_, _, ctx)
  local client = vim.lsp.get_client_by_id(ctx.client_id)
  for bufnr, _ in pairs(client and client.attached_buffers or {}) do
    draw_status(bufnr)
  end
  return vim.NIL
end

-- --------------------------------------------------------------- progress
-- $/progress from implement/verify is shown in the statusline, never through
-- messages (long messages would trigger the hit-enter prompt).
local progress_msg = ""
function _G.djinn_progress() return progress_msg end
vim.o.laststatus = 2
vim.o.statusline = "%<%f %m%r %=%#DjinnStatus#%{%v:lua.djinn_progress()%}%* %l:%c "
local function set_progress(msg)
  local width = math.max(20, vim.o.columns - 40)
  progress_msg = msg and (#msg > width and msg:sub(1, width - 1) .. "…" or msg) or ""
  vim.cmd.redrawstatus()
end
vim.api.nvim_create_autocmd("LspProgress", {
  callback = function(ev)
    local v = ev.data and ev.data.params and ev.data.params.value
    if not v then return end
    if v.kind == "begin" then
      set_progress("▶ " .. (v.title or "") .. " · " .. (v.message or ""))
    elseif v.kind == "end" then
      set_progress("■ " .. (v.title or "djinn") .. ": " .. (v.message or "done"))
      vim.defer_fn(function() set_progress("") end, 8000)
    else
      set_progress("▶ " .. (v.message or ""))
    end
  end,
})
-- window/showMessage: one line in the command area, no prompt
local orig_show_message = vim.lsp.handlers["window/showMessage"]
vim.lsp.handlers["window/showMessage"] = function(_, result, ctx)
  local client = vim.lsp.get_client_by_id(ctx.client_id)
  if client and client.name == "rust-djinn-lsp" then
    local first = (result.message or ""):gsub("\n.*", "")
    local width = math.max(20, vim.o.columns - 2)
    if #first > width then first = first:sub(1, width - 1) .. "…" end
    vim.api.nvim_echo({ { first, result.type <= 2 and "WarningMsg" or "DjinnStatusOk" } }, false, {})
    return vim.NIL
  end
  return orig_show_message(nil, result, ctx)
end

-- --------------------------------------------------------------- commands
local function enclosing_fn(bufnr)
  local row = vim.api.nvim_win_get_cursor(0)[1]
  for l = row, 1, -1 do
    local line = vim.api.nvim_buf_get_lines(bufnr, l - 1, l, false)[1] or ""
    local name = line:match("%f[%w_]fn%s+([%w_]+)%s*%(") or line:match("%f[%w_]rel%s+([%w_]+)%s*%(")
    if name then return name end
  end
end

local function djinn(command, with_name, extra)
  return function()
    local bufnr = vim.api.nvim_get_current_buf()
    local client = djinn_client(bufnr)
    if not client then return vim.notify("rust-djinn-lsp is not attached to this buffer", vim.log.levels.WARN) end
    local args = { vim.uri_from_bufnr(bufnr) }
    if with_name then table.insert(args, enclosing_fn(bufnr) or "") end
    for _, a in ipairs(extra or {}) do table.insert(args, a) end
    lsp_request(client, "workspace/executeCommand", { command = command, arguments = args }, function(err)
      if err then vim.notify(err.message or vim.inspect(err), vim.log.levels.ERROR) end
    end, bufnr)
  end
end

local map = function(keys, fn, desc) vim.keymap.set("n", keys, fn, { desc = desc }) end
map("<leader>di", djinn("djinn.implement", false, { AGENT }), "djinn: implement")
map("<leader>dv", djinn("djinn.verify"), "djinn: verify")
map("<leader>ds", djinn("djinn.smokeTest"), "djinn: smoke-test")
map("<leader>do", djinn("djinn.openObligations", true), "djinn: open obligations")
map("<leader>dp", djinn("djinn.openProofs", true), "djinn: open proofs")
map("<leader>dg", djinn("djinn.openGuide"), "djinn: guide")
map("<leader>dS", djinn("djinn.status"), "djinn: status")
map("<leader>dl", vim.lsp.codelens.run, "djinn: run a code lens on this line")

-- ------------------------------------------------------------ the servers
vim.api.nvim_create_autocmd("FileType", {
  pattern = "rust",
  callback = function(ev)
    local root = vim.fs.root(ev.buf, { "Cargo.toml" })
    if vim.fn.executable("rust-analyzer") == 1 then
      vim.lsp.start({
        name = "rust-analyzer",
        cmd = { "rust-analyzer" },
        root_dir = root,
        settings = { ["rust-analyzer"] = {
          inlayHints = { -- keep the Djinn hints readable
            typeHints = { enable = false }, parameterHints = { enable = false }, chainingHints = { enable = false },
          },
          -- analysis is exempt from Djinn's compile-time gate (unverified `fn`s
          -- are compile errors for `cargo build`); the status line shows them instead
          cargo = { extraEnv = { DJINN_GATE = "off" } },
        } },
      })
    end
    vim.lsp.start({
      name = "rust-djinn-lsp",
      cmd = { DJINN_LSP },
      init_options = { agent = AGENT },
      root_dir = root,
      handlers = { ["workspace/codeLens/refresh"] = on_lens_refresh, ["window/showMessage"] = vim.lsp.handlers["window/showMessage"] },
    })
  end,
})

vim.api.nvim_create_autocmd("LspAttach", {
  callback = function(ev)
    local client = vim.lsp.get_client_by_id(ev.data.client_id)
    if not client or client.name ~= "rust-djinn-lsp" then return end
    vim.lsp.inlay_hint.enable(INLINE_HINTS, { bufnr = ev.buf })
    draw_status(ev.buf)
    vim.api.nvim_create_autocmd({ "BufWritePost", "InsertLeave", "CursorHold" }, {
      buffer = ev.buf,
      callback = function() draw_status(ev.buf) end,
    })
    local timer = vim.uv.new_timer()
    timer:start(3000, 3000, vim.schedule_wrap(function()
      if vim.api.nvim_buf_is_valid(ev.buf) then draw_status(ev.buf) else timer:stop() end
    end))
  end,
})

(() => {
  // Piece constants
  const EMPTY = 0;
  const WP = 1, WN = 2, WB = 3, WR = 4, WQ = 5, WK = 6;
  const BP = 7, BN = 8, BB = 9, BR = 10, BQ = 11, BK = 12;

  const PIECE_UNICODE = {
    [WK]: '\u2654', [WQ]: '\u2655', [WR]: '\u2656', [WB]: '\u2657', [WN]: '\u2658', [WP]: '\u2659',
    [BK]: '\u265A', [BQ]: '\u265B', [BR]: '\u265C', [BB]: '\u265D', [BN]: '\u265E', [BP]: '\u265F'
  };

  const PIECE_LETTER = {
    [WN]: 'N', [WB]: 'B', [WR]: 'R', [WQ]: 'Q', [WK]: 'K',
    [BN]: 'N', [BB]: 'B', [BR]: 'R', [BQ]: 'Q', [BK]: 'K'
  };

  const PIECE_VALUE = {
    [WP]: 1, [WN]: 3, [WB]: 3, [WR]: 5, [WQ]: 9,
    [BP]: 1, [BN]: 3, [BB]: 3, [BR]: 5, [BQ]: 9
  };

  function isWhite(p) { return p >= WP && p <= WK; }
  function isBlack(p) { return p >= BP && p <= BK; }
  function colorOf(p) { return isWhite(p) ? 'w' : isBlack(p) ? 'b' : null; }
  function isAlly(p, turn) { return turn === 'w' ? isWhite(p) : isBlack(p); }
  function isEnemy(p, turn) { return turn === 'w' ? isBlack(p) : isWhite(p); }
  function inBounds(r, c) { return r >= 0 && r < 8 && c >= 0 && c < 8; }

  // DOM
  const boardEl = document.getElementById('board');
  const statusEl = document.getElementById('status');
  const moveLogEl = document.getElementById('move-log');
  const blackCapturedEl = document.getElementById('black-captured');
  const whiteCapturedEl = document.getElementById('white-captured');
  const whiteLabelEl = document.getElementById('white-label');
  const blackLabelEl = document.getElementById('black-label');
  const promoModal = document.getElementById('promotion-modal');
  const promoChoices = promoModal.querySelector('.promotion-choices');
  const newGameBtn = document.getElementById('new-game-btn');
  const undoBtn = document.getElementById('undo-btn');

  let board, turn, selected, legalMoves, history, moveList;
  let castleRights, enPassant, halfmove, fullmove, gameOver;
  let whiteCaptured, blackCaptured, lastMove;

  const INIT_BOARD = [
    [BR, BN, BB, BQ, BK, BB, BN, BR],
    [BP, BP, BP, BP, BP, BP, BP, BP],
    [0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0],
    [WP, WP, WP, WP, WP, WP, WP, WP],
    [WR, WN, WB, WQ, WK, WB, WN, WR]
  ];

  function init() {
    board = INIT_BOARD.map(r => [...r]);
    turn = 'w';
    selected = null;
    legalMoves = [];
    history = [];
    moveList = [];
    castleRights = { wK: true, wQ: true, bK: true, bQ: true };
    enPassant = null;
    halfmove = 0;
    fullmove = 1;
    gameOver = false;
    whiteCaptured = [];
    blackCaptured = [];
    lastMove = null;
    render();
    updateStatus();
    moveLogEl.innerHTML = '';
  }

  // ---- MOVE GENERATION ----

  function pseudoLegalMoves(b, t, ep, castle) {
    const moves = [];
    const dir = t === 'w' ? -1 : 1;
    const startRow = t === 'w' ? 6 : 1;
    const promoRow = t === 'w' ? 0 : 7;

    for (let r = 0; r < 8; r++) {
      for (let c = 0; c < 8; c++) {
        const p = b[r][c];
        if (!isAlly(p, t)) continue;

        const type = isWhite(p) ? p : p - 6;

        if (type === WP) {
          // Forward
          if (inBounds(r + dir, c) && b[r + dir][c] === EMPTY) {
            addPawnMoves(moves, r, c, r + dir, c, promoRow, t);
            // Double push
            if (r === startRow && b[r + dir * 2][c] === EMPTY) {
              moves.push({ fr: r, fc: c, tr: r + dir * 2, tc: c });
            }
          }
          // Captures
          for (const dc of [-1, 1]) {
            const nr = r + dir, nc = c + dc;
            if (!inBounds(nr, nc)) continue;
            if (isEnemy(b[nr][nc], t)) {
              addPawnMoves(moves, r, c, nr, nc, promoRow, t);
            }
            // En passant
            if (ep && ep.r === nr && ep.c === nc) {
              moves.push({ fr: r, fc: c, tr: nr, tc: nc, ep: true });
            }
          }
        }
        else if (type === WN) {
          for (const [dr, dc] of [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]]) {
            const nr = r + dr, nc = c + dc;
            if (inBounds(nr, nc) && !isAlly(b[nr][nc], t))
              moves.push({ fr: r, fc: c, tr: nr, tc: nc });
          }
        }
        else if (type === WB) {
          slideMoves(b, t, r, c, [[-1,-1],[-1,1],[1,-1],[1,1]], moves);
        }
        else if (type === WR) {
          slideMoves(b, t, r, c, [[-1,0],[1,0],[0,-1],[0,1]], moves);
        }
        else if (type === WQ) {
          slideMoves(b, t, r, c, [[-1,-1],[-1,1],[1,-1],[1,1],[-1,0],[1,0],[0,-1],[0,1]], moves);
        }
        else if (type === WK) {
          for (let dr = -1; dr <= 1; dr++)
            for (let dc = -1; dc <= 1; dc++) {
              if (dr === 0 && dc === 0) continue;
              const nr = r + dr, nc = c + dc;
              if (inBounds(nr, nc) && !isAlly(b[nr][nc], t))
                moves.push({ fr: r, fc: c, tr: nr, tc: nc });
            }
          // Castling
          const row = t === 'w' ? 7 : 0;
          const ks = t === 'w' ? 'wK' : 'bK';
          const qs = t === 'w' ? 'wQ' : 'bQ';
          if (r === row && c === 4) {
            if (castle[ks] && b[row][5] === EMPTY && b[row][6] === EMPTY && b[row][7] === (t === 'w' ? WR : BR)) {
              if (!isSquareAttacked(b, row, 4, t) && !isSquareAttacked(b, row, 5, t) && !isSquareAttacked(b, row, 6, t))
                moves.push({ fr: r, fc: c, tr: row, tc: 6, castle: 'K' });
            }
            if (castle[qs] && b[row][3] === EMPTY && b[row][2] === EMPTY && b[row][1] === EMPTY && b[row][0] === (t === 'w' ? WR : BR)) {
              if (!isSquareAttacked(b, row, 4, t) && !isSquareAttacked(b, row, 3, t) && !isSquareAttacked(b, row, 2, t))
                moves.push({ fr: r, fc: c, tr: row, tc: 2, castle: 'Q' });
            }
          }
        }
      }
    }
    return moves;
  }

  function addPawnMoves(moves, fr, fc, tr, tc, promoRow, t) {
    if (tr === promoRow) {
      const pieces = t === 'w' ? [WQ, WR, WB, WN] : [BQ, BR, BB, BN];
      for (const pp of pieces)
        moves.push({ fr, fc, tr, tc, promo: pp });
    } else {
      moves.push({ fr, fc, tr, tc });
    }
  }

  function slideMoves(b, t, r, c, dirs, moves) {
    for (const [dr, dc] of dirs) {
      let nr = r + dr, nc = c + dc;
      while (inBounds(nr, nc)) {
        if (isAlly(b[nr][nc], t)) break;
        moves.push({ fr: r, fc: c, tr: nr, tc: nc });
        if (isEnemy(b[nr][nc], t)) break;
        nr += dr;
        nc += dc;
      }
    }
  }

  function isSquareAttacked(b, r, c, byColor) {
    // byColor is the defender; attacker is opposite
    const attacker = byColor === 'w' ? 'b' : 'w';
    const aDir = attacker === 'w' ? -1 : 1;

    // Pawn attacks
    for (const dc of [-1, 1]) {
      const pr = r - aDir, pc = c + dc;
      if (inBounds(pr, pc)) {
        const p = b[pr][pc];
        if ((attacker === 'w' && p === WP) || (attacker === 'b' && p === BP)) return true;
      }
    }

    // Knight
    for (const [dr, dc] of [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]]) {
      const nr = r + dr, nc = c + dc;
      if (inBounds(nr, nc)) {
        const p = b[nr][nc];
        if ((attacker === 'w' && p === WN) || (attacker === 'b' && p === BN)) return true;
      }
    }

    // King
    for (let dr = -1; dr <= 1; dr++)
      for (let dc = -1; dc <= 1; dc++) {
        if (dr === 0 && dc === 0) continue;
        const nr = r + dr, nc = c + dc;
        if (inBounds(nr, nc)) {
          const p = b[nr][nc];
          if ((attacker === 'w' && p === WK) || (attacker === 'b' && p === BK)) return true;
        }
      }

    // Slides: bishop/queen diagonals, rook/queen straights
    const diagPieces = attacker === 'w' ? [WB, WQ] : [BB, BQ];
    const straightPieces = attacker === 'w' ? [WR, WQ] : [BR, BQ];

    for (const [dr, dc] of [[-1,-1],[-1,1],[1,-1],[1,1]]) {
      let nr = r + dr, nc = c + dc;
      while (inBounds(nr, nc)) {
        const p = b[nr][nc];
        if (p !== EMPTY) {
          if (diagPieces.includes(p)) return true;
          break;
        }
        nr += dr; nc += dc;
      }
    }

    for (const [dr, dc] of [[-1,0],[1,0],[0,-1],[0,1]]) {
      let nr = r + dr, nc = c + dc;
      while (inBounds(nr, nc)) {
        const p = b[nr][nc];
        if (p !== EMPTY) {
          if (straightPieces.includes(p)) return true;
          break;
        }
        nr += dr; nc += dc;
      }
    }

    return false;
  }

  function findKing(b, t) {
    const king = t === 'w' ? WK : BK;
    for (let r = 0; r < 8; r++)
      for (let c = 0; c < 8; c++)
        if (b[r][c] === king) return { r, c };
    return null;
  }

  function inCheck(b, t) {
    const k = findKing(b, t);
    return k && isSquareAttacked(b, k.r, k.c, t);
  }

  function makeMove(b, m) {
    const nb = b.map(r => [...r]);
    const captured = nb[m.tr][m.tc];
    nb[m.tr][m.tc] = nb[m.fr][m.fc];
    nb[m.fr][m.fc] = EMPTY;

    if (m.promo) nb[m.tr][m.tc] = m.promo;

    if (m.ep) {
      const epRow = m.tr === 2 ? 3 : 5;
      nb[epRow][m.tc] = EMPTY;
    }

    if (m.castle === 'K') {
      const row = m.tr;
      nb[row][5] = nb[row][7];
      nb[row][7] = EMPTY;
    } else if (m.castle === 'Q') {
      const row = m.tr;
      nb[row][3] = nb[row][0];
      nb[row][0] = EMPTY;
    }

    return nb;
  }

  function getLegalMoves(b, t, ep, castle) {
    const pseudo = pseudoLegalMoves(b, t, ep, castle);
    return pseudo.filter(m => {
      const nb = makeMove(b, m);
      return !inCheck(nb, t);
    });
  }

  // ---- GAME LOGIC ----

  function handleSquareClick(r, c) {
    if (gameOver) return;

    const piece = board[r][c];

    if (selected) {
      // Try to move
      const move = legalMoves.find(m => m.tr === r && m.tc === c);
      if (move) {
        // Check for promotion choice needed
        if (move.promo !== undefined) {
          // Is there a promotion on this square?
          const promos = legalMoves.filter(m => m.tr === r && m.tc === c && m.promo);
          if (promos.length > 1) {
            showPromotion(promos);
            return;
          }
        }
        executeMove(move);
        return;
      }

      // Clicked own piece — reselect
      if (isAlly(piece, turn)) {
        selectPiece(r, c);
        return;
      }

      // Clicked empty/invalid — deselect
      selected = null;
      legalMoves = [];
      render();
      return;
    }

    // Select piece
    if (isAlly(piece, turn)) {
      selectPiece(r, c);
    }
  }

  function selectPiece(r, c) {
    selected = { r, c };
    const allLegal = getLegalMoves(board, turn, enPassant, castleRights);
    legalMoves = allLegal.filter(m => m.fr === r && m.fc === c);
    render();
  }

  function executeMove(move) {
    // Save state for undo
    history.push({
      board: board.map(r => [...r]),
      turn, castleRights: { ...castleRights },
      enPassant: enPassant ? { ...enPassant } : null,
      halfmove, fullmove,
      whiteCaptured: [...whiteCaptured],
      blackCaptured: [...blackCaptured],
      lastMove
    });

    const captured = board[move.tr][move.tc];
    const movingPiece = board[move.fr][move.fc];

    // Track captures
    if (captured !== EMPTY) {
      if (isWhite(captured)) blackCaptured.push(captured);
      else whiteCaptured.push(captured);
    }
    if (move.ep) {
      if (turn === 'w') whiteCaptured.push(BP);
      else blackCaptured.push(WP);
    }

    // Build notation before making the move
    const notation = buildNotation(move, movingPiece, captured);

    // Make the move
    board = makeMove(board, move);

    // Update castling rights
    if (movingPiece === WK) { castleRights.wK = false; castleRights.wQ = false; }
    if (movingPiece === BK) { castleRights.bK = false; castleRights.bQ = false; }
    if (movingPiece === WR && move.fr === 7 && move.fc === 0) castleRights.wQ = false;
    if (movingPiece === WR && move.fr === 7 && move.fc === 7) castleRights.wK = false;
    if (movingPiece === BR && move.fr === 0 && move.fc === 0) castleRights.bQ = false;
    if (movingPiece === BR && move.fr === 0 && move.fc === 7) castleRights.bK = false;
    // Rook captured
    if (move.tr === 7 && move.tc === 0) castleRights.wQ = false;
    if (move.tr === 7 && move.tc === 7) castleRights.wK = false;
    if (move.tr === 0 && move.tc === 0) castleRights.bQ = false;
    if (move.tr === 0 && move.tc === 7) castleRights.bK = false;

    // En passant
    const pt = isWhite(movingPiece) ? movingPiece : movingPiece - 6;
    if (pt === WP && Math.abs(move.tr - move.fr) === 2) {
      enPassant = { r: (move.fr + move.tr) / 2, c: move.fc };
    } else {
      enPassant = null;
    }

    // Halfmove clock
    if (pt === WP || captured !== EMPTY || move.ep) halfmove = 0;
    else halfmove++;

    lastMove = { fr: move.fr, fc: move.fc, tr: move.tr, tc: move.tc };

    // Switch turn
    turn = turn === 'w' ? 'b' : 'w';
    if (turn === 'w') fullmove++;

    selected = null;
    legalMoves = [];

    // Check for game end
    const opponentMoves = getLegalMoves(board, turn, enPassant, castleRights);
    const check = inCheck(board, turn);
    let suffix = '';

    if (opponentMoves.length === 0) {
      gameOver = true;
      if (check) {
        suffix = '#';
      } else {
        suffix = '';
      }
    } else if (check) {
      suffix = '+';
    }

    // Fifty move rule
    if (halfmove >= 100) {
      gameOver = true;
    }

    // Insufficient material
    if (isInsufficientMaterial()) {
      gameOver = true;
    }

    logMove(notation + suffix);
    render();
    updateStatus();
  }

  function buildNotation(move, piece, captured) {
    if (move.castle === 'K') return 'O-O';
    if (move.castle === 'Q') return 'O-O-O';

    let n = '';
    const letter = PIECE_LETTER[piece] || '';
    const isCapture = captured !== EMPTY || move.ep;
    const pt = isWhite(piece) ? piece : piece - 6;

    if (pt === WP) {
      if (isCapture) n += String.fromCharCode(97 + move.fc);
    } else {
      n += letter;
    }

    if (isCapture) n += 'x';
    n += String.fromCharCode(97 + move.tc) + (8 - move.tr);

    if (move.promo) {
      n += '=' + PIECE_LETTER[move.promo];
    }

    return n;
  }

  function logMove(notation) {
    if (turn === 'b') {
      // White just moved
      moveList.push({ num: fullmove - (turn === 'b' ? 0 : 1), w: notation, b: null });
    } else {
      // Black just moved
      if (moveList.length > 0) {
        moveList[moveList.length - 1].b = notation;
      }
    }
    renderMoveLog();
  }

  function renderMoveLog() {
    moveLogEl.innerHTML = moveList.map(m =>
      `<span class="move-num">${m.num}.</span><span class="white-move">${m.w}</span>${m.b ? `<span class="black-move">${m.b}</span>` : ''}`
    ).join(' ');
    moveLogEl.scrollTop = moveLogEl.scrollHeight;
  }

  function isInsufficientMaterial() {
    const pieces = [];
    for (let r = 0; r < 8; r++)
      for (let c = 0; c < 8; c++)
        if (board[r][c] !== EMPTY) pieces.push(board[r][c]);

    if (pieces.length === 2) return true; // K vs K
    if (pieces.length === 3) {
      // K+B vs K or K+N vs K
      for (const p of pieces) {
        const t = isWhite(p) ? p : p - 6;
        if (t === WB || t === WN) return true;
      }
    }
    return false;
  }

  function showPromotion(promos) {
    promoChoices.innerHTML = '';
    for (const m of promos) {
      const btn = document.createElement('button');
      btn.className = 'promo-option';
      btn.textContent = PIECE_UNICODE[m.promo];
      btn.addEventListener('click', () => {
        promoModal.classList.add('hidden');
        executeMove(m);
      });
      promoChoices.appendChild(btn);
    }
    promoModal.classList.remove('hidden');
  }

  function undo() {
    if (history.length === 0) return;
    const state = history.pop();
    board = state.board;
    turn = state.turn;
    castleRights = state.castleRights;
    enPassant = state.enPassant;
    halfmove = state.halfmove;
    fullmove = state.fullmove;
    whiteCaptured = state.whiteCaptured;
    blackCaptured = state.blackCaptured;
    lastMove = state.lastMove;
    gameOver = false;
    selected = null;
    legalMoves = [];

    // Remove last move from log
    if (moveList.length > 0) {
      const last = moveList[moveList.length - 1];
      if (last.b !== null) {
        last.b = null;
      } else {
        moveList.pop();
      }
    }

    render();
    renderMoveLog();
    updateStatus();
  }

  function updateStatus() {
    const check = inCheck(board, turn);
    const legal = getLegalMoves(board, turn, enPassant, castleRights);

    whiteLabelEl.classList.toggle('active-player', turn === 'w');
    blackLabelEl.classList.toggle('active-player', turn === 'b');

    if (legal.length === 0 && check) {
      const winner = turn === 'w' ? 'Black' : 'White';
      statusEl.textContent = `Checkmate — ${winner} wins!`;
      statusEl.className = 'status win';
    } else if (legal.length === 0) {
      statusEl.textContent = 'Stalemate — Draw';
      statusEl.className = 'status draw';
    } else if (halfmove >= 100) {
      statusEl.textContent = '50-move rule — Draw';
      statusEl.className = 'status draw';
    } else if (isInsufficientMaterial()) {
      statusEl.textContent = 'Insufficient material — Draw';
      statusEl.className = 'status draw';
    } else if (check) {
      statusEl.textContent = `${turn === 'w' ? 'White' : 'Black'} is in check!`;
      statusEl.className = 'status check';
    } else {
      statusEl.textContent = `${turn === 'w' ? 'White' : 'Black'} to move`;
      statusEl.className = 'status';
    }
  }

  // ---- RENDER ----

  function render() {
    boardEl.innerHTML = '';
    const kingPos = findKing(board, turn);
    const check = inCheck(board, turn);

    for (let r = 0; r < 8; r++) {
      for (let c = 0; c < 8; c++) {
        const sq = document.createElement('div');
        const isLight = (r + c) % 2 === 0;
        sq.className = `square ${isLight ? 'light' : 'dark'}`;

        // Last move highlight
        if (lastMove && ((r === lastMove.fr && c === lastMove.fc) || (r === lastMove.tr && c === lastMove.tc))) {
          sq.classList.add('last-move');
        }

        // Selected
        if (selected && r === selected.r && c === selected.c) {
          sq.classList.add('selected');
        }

        // Legal move dots
        const isLegal = legalMoves.some(m => m.tr === r && m.tc === c);
        if (isLegal) {
          if (board[r][c] !== EMPTY || (enPassant && legalMoves.some(m => m.tr === r && m.tc === c && m.ep))) {
            sq.classList.add('legal-capture');
          } else {
            sq.classList.add('legal-move');
          }
        }

        // King in check
        if (check && kingPos && r === kingPos.r && c === kingPos.c) {
          sq.classList.add('in-check');
        }

        // Piece
        if (board[r][c] !== EMPTY) {
          const span = document.createElement('span');
          span.className = 'piece';
          span.textContent = PIECE_UNICODE[board[r][c]];
          sq.appendChild(span);
        }

        sq.addEventListener('click', () => handleSquareClick(r, c));
        boardEl.appendChild(sq);
      }
    }

    // Captured pieces
    const sortCaptures = arr => [...arr].sort((a, b) => (PIECE_VALUE[b] || 0) - (PIECE_VALUE[a] || 0));
    whiteCapturedEl.innerHTML = sortCaptures(whiteCaptured).map(p => PIECE_UNICODE[p]).join('');
    blackCapturedEl.innerHTML = sortCaptures(blackCaptured).map(p => PIECE_UNICODE[p]).join('');
  }

  // Events
  newGameBtn.addEventListener('click', init);
  undoBtn.addEventListener('click', undo);

  init();
})();

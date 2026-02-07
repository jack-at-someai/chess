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

  // Material values for evaluation (centipawns)
  const MAT = { [WP]: 100, [WN]: 320, [WB]: 330, [WR]: 500, [WQ]: 900, [WK]: 20000,
                 [BP]: 100, [BN]: 320, [BB]: 330, [BR]: 500, [BQ]: 900, [BK]: 20000 };

  // Piece-square tables (from white's perspective, index [row][col], row 0 = rank 8)
  const PST_PAWN = [
    [ 0,  0,  0,  0,  0,  0,  0,  0],
    [50, 50, 50, 50, 50, 50, 50, 50],
    [10, 10, 20, 30, 30, 20, 10, 10],
    [ 5,  5, 10, 25, 25, 10,  5,  5],
    [ 0,  0,  0, 20, 20,  0,  0,  0],
    [ 5, -5,-10,  0,  0,-10, -5,  5],
    [ 5, 10, 10,-20,-20, 10, 10,  5],
    [ 0,  0,  0,  0,  0,  0,  0,  0]
  ];
  const PST_KNIGHT = [
    [-50,-40,-30,-30,-30,-30,-40,-50],
    [-40,-20,  0,  0,  0,  0,-20,-40],
    [-30,  0, 10, 15, 15, 10,  0,-30],
    [-30,  5, 15, 20, 20, 15,  5,-30],
    [-30,  0, 15, 20, 20, 15,  0,-30],
    [-30,  5, 10, 15, 15, 10,  5,-30],
    [-40,-20,  0,  5,  5,  0,-20,-40],
    [-50,-40,-30,-30,-30,-30,-40,-50]
  ];
  const PST_BISHOP = [
    [-20,-10,-10,-10,-10,-10,-10,-20],
    [-10,  0,  0,  0,  0,  0,  0,-10],
    [-10,  0, 10, 10, 10, 10,  0,-10],
    [-10,  5,  5, 10, 10,  5,  5,-10],
    [-10,  0,  5, 10, 10,  5,  0,-10],
    [-10, 10, 10, 10, 10, 10, 10,-10],
    [-10,  5,  0,  0,  0,  0,  5,-10],
    [-20,-10,-10,-10,-10,-10,-10,-20]
  ];
  const PST_ROOK = [
    [ 0,  0,  0,  0,  0,  0,  0,  0],
    [ 5, 10, 10, 10, 10, 10, 10,  5],
    [-5,  0,  0,  0,  0,  0,  0, -5],
    [-5,  0,  0,  0,  0,  0,  0, -5],
    [-5,  0,  0,  0,  0,  0,  0, -5],
    [-5,  0,  0,  0,  0,  0,  0, -5],
    [-5,  0,  0,  0,  0,  0,  0, -5],
    [ 0,  0,  0,  5,  5,  0,  0,  0]
  ];
  const PST_QUEEN = [
    [-20,-10,-10, -5, -5,-10,-10,-20],
    [-10,  0,  0,  0,  0,  0,  0,-10],
    [-10,  0,  5,  5,  5,  5,  0,-10],
    [ -5,  0,  5,  5,  5,  5,  0, -5],
    [  0,  0,  5,  5,  5,  5,  0, -5],
    [-10,  5,  5,  5,  5,  5,  0,-10],
    [-10,  0,  5,  0,  0,  0,  0,-10],
    [-20,-10,-10, -5, -5,-10,-10,-20]
  ];
  const PST_KING_MG = [
    [-30,-40,-40,-50,-50,-40,-40,-30],
    [-30,-40,-40,-50,-50,-40,-40,-30],
    [-30,-40,-40,-50,-50,-40,-40,-30],
    [-30,-40,-40,-50,-50,-40,-40,-30],
    [-20,-30,-30,-40,-40,-30,-30,-20],
    [-10,-20,-20,-20,-20,-20,-20,-10],
    [ 20, 20,  0,  0,  0,  0, 20, 20],
    [ 20, 30, 10,  0,  0, 10, 30, 20]
  ];

  function getPST(piece) {
    const type = isWhite(piece) ? piece : piece - 6;
    switch (type) {
      case WP: return PST_PAWN;
      case WN: return PST_KNIGHT;
      case WB: return PST_BISHOP;
      case WR: return PST_ROOK;
      case WQ: return PST_QUEEN;
      case WK: return PST_KING_MG;
      default: return null;
    }
  }

  function isWhite(p) { return p >= WP && p <= WK; }
  function isBlack(p) { return p >= BP && p <= BK; }
  function isAlly(p, turn) { return turn === 'w' ? isWhite(p) : isBlack(p); }
  function isEnemy(p, turn) { return turn === 'w' ? isBlack(p) : isWhite(p); }
  function inBounds(r, c) { return r >= 0 && r < 8 && c >= 0 && c < 8; }

  const HUMAN = 'w';
  const AI_COLOR = 'b';
  const AI_DEPTH = 3;

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
  let whiteCaptured, blackCaptured, lastMove, aiThinking;

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
    aiThinking = false;
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
          if (inBounds(r + dir, c) && b[r + dir][c] === EMPTY) {
            addPawnMoves(moves, r, c, r + dir, c, promoRow, t);
            if (r === startRow && b[r + dir * 2][c] === EMPTY)
              moves.push({ fr: r, fc: c, tr: r + dir * 2, tc: c });
          }
          for (const dc of [-1, 1]) {
            const nr = r + dir, nc = c + dc;
            if (!inBounds(nr, nc)) continue;
            if (isEnemy(b[nr][nc], t))
              addPawnMoves(moves, r, c, nr, nc, promoRow, t);
            if (ep && ep.r === nr && ep.c === nc)
              moves.push({ fr: r, fc: c, tr: nr, tc: nc, ep: true });
          }
        }
        else if (type === WN) {
          for (const [dr, dc] of [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]]) {
            const nr = r + dr, nc = c + dc;
            if (inBounds(nr, nc) && !isAlly(b[nr][nc], t))
              moves.push({ fr: r, fc: c, tr: nr, tc: nc });
          }
        }
        else if (type === WB) slideMoves(b, t, r, c, [[-1,-1],[-1,1],[1,-1],[1,1]], moves);
        else if (type === WR) slideMoves(b, t, r, c, [[-1,0],[1,0],[0,-1],[0,1]], moves);
        else if (type === WQ) slideMoves(b, t, r, c, [[-1,-1],[-1,1],[1,-1],[1,1],[-1,0],[1,0],[0,-1],[0,1]], moves);
        else if (type === WK) {
          for (let dr = -1; dr <= 1; dr++)
            for (let dc = -1; dc <= 1; dc++) {
              if (dr === 0 && dc === 0) continue;
              const nr = r + dr, nc = c + dc;
              if (inBounds(nr, nc) && !isAlly(b[nr][nc], t))
                moves.push({ fr: r, fc: c, tr: nr, tc: nc });
            }
          const row = t === 'w' ? 7 : 0;
          const ks = t === 'w' ? 'wK' : 'bK';
          const qs = t === 'w' ? 'wQ' : 'bQ';
          if (r === row && c === 4) {
            if (castle[ks] && b[row][5] === EMPTY && b[row][6] === EMPTY && b[row][7] === (t === 'w' ? WR : BR))
              if (!isSquareAttacked(b, row, 4, t) && !isSquareAttacked(b, row, 5, t) && !isSquareAttacked(b, row, 6, t))
                moves.push({ fr: r, fc: c, tr: row, tc: 6, castle: 'K' });
            if (castle[qs] && b[row][3] === EMPTY && b[row][2] === EMPTY && b[row][1] === EMPTY && b[row][0] === (t === 'w' ? WR : BR))
              if (!isSquareAttacked(b, row, 4, t) && !isSquareAttacked(b, row, 3, t) && !isSquareAttacked(b, row, 2, t))
                moves.push({ fr: r, fc: c, tr: row, tc: 2, castle: 'Q' });
          }
        }
      }
    }
    return moves;
  }

  function addPawnMoves(moves, fr, fc, tr, tc, promoRow, t) {
    if (tr === promoRow) {
      const pieces = t === 'w' ? [WQ, WR, WB, WN] : [BQ, BR, BB, BN];
      for (const pp of pieces) moves.push({ fr, fc, tr, tc, promo: pp });
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
        nr += dr; nc += dc;
      }
    }
  }

  function isSquareAttacked(b, r, c, byColor) {
    const attacker = byColor === 'w' ? 'b' : 'w';
    const aDir = attacker === 'w' ? -1 : 1;
    for (const dc of [-1, 1]) {
      const pr = r - aDir, pc = c + dc;
      if (inBounds(pr, pc)) {
        const p = b[pr][pc];
        if ((attacker === 'w' && p === WP) || (attacker === 'b' && p === BP)) return true;
      }
    }
    for (const [dr, dc] of [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]]) {
      const nr = r + dr, nc = c + dc;
      if (inBounds(nr, nc)) {
        const p = b[nr][nc];
        if ((attacker === 'w' && p === WN) || (attacker === 'b' && p === BN)) return true;
      }
    }
    for (let dr = -1; dr <= 1; dr++)
      for (let dc = -1; dc <= 1; dc++) {
        if (dr === 0 && dc === 0) continue;
        const nr = r + dr, nc = c + dc;
        if (inBounds(nr, nc)) {
          const p = b[nr][nc];
          if ((attacker === 'w' && p === WK) || (attacker === 'b' && p === BK)) return true;
        }
      }
    const diagPieces = attacker === 'w' ? [WB, WQ] : [BB, BQ];
    const straightPieces = attacker === 'w' ? [WR, WQ] : [BR, BQ];
    for (const [dr, dc] of [[-1,-1],[-1,1],[1,-1],[1,1]]) {
      let nr = r + dr, nc = c + dc;
      while (inBounds(nr, nc)) {
        const p = b[nr][nc];
        if (p !== EMPTY) { if (diagPieces.includes(p)) return true; break; }
        nr += dr; nc += dc;
      }
    }
    for (const [dr, dc] of [[-1,0],[1,0],[0,-1],[0,1]]) {
      let nr = r + dr, nc = c + dc;
      while (inBounds(nr, nc)) {
        const p = b[nr][nc];
        if (p !== EMPTY) { if (straightPieces.includes(p)) return true; break; }
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
    nb[m.tr][m.tc] = nb[m.fr][m.fc];
    nb[m.fr][m.fc] = EMPTY;
    if (m.promo) nb[m.tr][m.tc] = m.promo;
    if (m.ep) {
      const epRow = m.tr === 2 ? 3 : 5;
      nb[epRow][m.tc] = EMPTY;
    }
    if (m.castle === 'K') { nb[m.tr][5] = nb[m.tr][7]; nb[m.tr][7] = EMPTY; }
    else if (m.castle === 'Q') { nb[m.tr][3] = nb[m.tr][0]; nb[m.tr][0] = EMPTY; }
    return nb;
  }

  function getLegalMoves(b, t, ep, castle) {
    return pseudoLegalMoves(b, t, ep, castle).filter(m => !inCheck(makeMove(b, m), t));
  }

  // ---- AI: MINIMAX WITH ALPHA-BETA ----

  function evaluate(b) {
    let score = 0;
    for (let r = 0; r < 8; r++) {
      for (let c = 0; c < 8; c++) {
        const p = b[r][c];
        if (p === EMPTY) continue;
        const pst = getPST(p);
        if (isWhite(p)) {
          score += MAT[p];
          if (pst) score += pst[r][c];
        } else {
          score -= MAT[p];
          if (pst) score -= pst[7 - r][c]; // mirror for black
        }
      }
    }
    return score;
  }

  function updateCastleRights(castle, piece, move) {
    const nc = { ...castle };
    if (piece === WK) { nc.wK = false; nc.wQ = false; }
    if (piece === BK) { nc.bK = false; nc.bQ = false; }
    if (piece === WR && move.fr === 7 && move.fc === 0) nc.wQ = false;
    if (piece === WR && move.fr === 7 && move.fc === 7) nc.wK = false;
    if (piece === BR && move.fr === 0 && move.fc === 0) nc.bQ = false;
    if (piece === BR && move.fr === 0 && move.fc === 7) nc.bK = false;
    if (move.tr === 7 && move.tc === 0) nc.wQ = false;
    if (move.tr === 7 && move.tc === 7) nc.wK = false;
    if (move.tr === 0 && move.tc === 0) nc.bQ = false;
    if (move.tr === 0 && move.tc === 7) nc.bK = false;
    return nc;
  }

  function getNewEP(piece, move) {
    const pt = isWhite(piece) ? piece : piece - 6;
    if (pt === WP && Math.abs(move.tr - move.fr) === 2)
      return { r: (move.fr + move.tr) / 2, c: move.fc };
    return null;
  }

  // Move ordering heuristic for better pruning
  function scoreMove(b, m) {
    let s = 0;
    const captured = b[m.tr][m.tc];
    if (captured !== EMPTY) s += MAT[captured] * 10; // captures first
    if (m.promo) s += MAT[m.promo];
    if (m.castle) s += 50;
    return s;
  }

  function minimax(b, t, ep, castle, depth, alpha, beta, maximizing) {
    const moves = getLegalMoves(b, t, ep, castle);
    if (moves.length === 0) {
      if (inCheck(b, t)) return maximizing ? -99999 + (AI_DEPTH - depth) : 99999 - (AI_DEPTH - depth);
      return 0; // stalemate
    }
    if (depth === 0) return evaluate(b);

    // Order moves
    moves.sort((a, bb) => scoreMove(b, bb) - scoreMove(b, a));

    if (maximizing) {
      let best = -Infinity;
      for (const m of moves) {
        const nb = makeMove(b, m);
        const piece = b[m.fr][m.fc];
        const nc = updateCastleRights(castle, piece, m);
        const nep = getNewEP(piece, m);
        const val = minimax(nb, t === 'w' ? 'b' : 'w', nep, nc, depth - 1, alpha, beta, false);
        best = Math.max(best, val);
        alpha = Math.max(alpha, val);
        if (beta <= alpha) break;
      }
      return best;
    } else {
      let best = Infinity;
      for (const m of moves) {
        const nb = makeMove(b, m);
        const piece = b[m.fr][m.fc];
        const nc = updateCastleRights(castle, piece, m);
        const nep = getNewEP(piece, m);
        const val = minimax(nb, t === 'w' ? 'b' : 'w', nep, nc, depth - 1, alpha, beta, true);
        best = Math.min(best, val);
        beta = Math.min(beta, val);
        if (beta <= alpha) break;
      }
      return best;
    }
  }

  function aiBestMove() {
    const moves = getLegalMoves(board, AI_COLOR, enPassant, castleRights);
    if (moves.length === 0) return null;

    // Order moves
    moves.sort((a, b) => scoreMove(board, b) - scoreMove(board, a));

    let bestScore = Infinity; // AI is minimizing (black)
    let bestMove = moves[0];

    for (const m of moves) {
      const nb = makeMove(board, m);
      const piece = board[m.fr][m.fc];
      const nc = updateCastleRights(castleRights, piece, m);
      const nep = getNewEP(piece, m);
      // AI (black) is minimizing, so next call is white maximizing
      const score = minimax(nb, 'w', nep, nc, AI_DEPTH - 1, -Infinity, Infinity, true);
      if (score < bestScore) {
        bestScore = score;
        bestMove = m;
      }
    }
    return bestMove;
  }

  // ---- GAME LOGIC ----

  function handleSquareClick(r, c) {
    if (gameOver || aiThinking || turn !== HUMAN) return;

    const piece = board[r][c];

    if (selected) {
      const move = legalMoves.find(m => m.tr === r && m.tc === c);
      if (move) {
        if (move.promo !== undefined) {
          const promos = legalMoves.filter(m => m.tr === r && m.tc === c && m.promo);
          if (promos.length > 1) { showPromotion(promos); return; }
        }
        executeMove(move);
        return;
      }
      if (isAlly(piece, turn)) { selectPiece(r, c); return; }
      selected = null;
      legalMoves = [];
      render();
      return;
    }

    if (isAlly(piece, turn)) selectPiece(r, c);
  }

  function selectPiece(r, c) {
    selected = { r, c };
    const allLegal = getLegalMoves(board, turn, enPassant, castleRights);
    legalMoves = allLegal.filter(m => m.fr === r && m.fc === c);
    render();
  }

  function executeMove(move) {
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

    if (captured !== EMPTY) {
      if (isWhite(captured)) blackCaptured.push(captured);
      else whiteCaptured.push(captured);
    }
    if (move.ep) {
      if (turn === 'w') whiteCaptured.push(BP);
      else blackCaptured.push(WP);
    }

    const notation = buildNotation(move, movingPiece, captured);
    board = makeMove(board, move);

    castleRights = updateCastleRights(castleRights, movingPiece, move);
    enPassant = getNewEP(movingPiece, move);

    const pt = isWhite(movingPiece) ? movingPiece : movingPiece - 6;
    if (pt === WP || captured !== EMPTY || move.ep) halfmove = 0;
    else halfmove++;

    lastMove = { fr: move.fr, fc: move.fc, tr: move.tr, tc: move.tc };
    turn = turn === 'w' ? 'b' : 'w';
    if (turn === 'w') fullmove++;

    selected = null;
    legalMoves = [];

    const opponentMoves = getLegalMoves(board, turn, enPassant, castleRights);
    const check = inCheck(board, turn);
    let suffix = '';

    if (opponentMoves.length === 0) {
      gameOver = true;
      suffix = check ? '#' : '';
    } else if (check) {
      suffix = '+';
    }

    if (halfmove >= 100) gameOver = true;
    if (isInsufficientMaterial()) gameOver = true;

    logMove(notation + suffix);
    render();
    updateStatus();

    // Trigger AI
    if (!gameOver && turn === AI_COLOR) {
      aiThinking = true;
      statusEl.textContent = 'AI is thinking...';
      setTimeout(() => {
        const aiMove = aiBestMove();
        if (aiMove) {
          // AI always promotes to queen
          executeMove(aiMove);
        }
        aiThinking = false;
      }, 50);
    }
  }

  function buildNotation(move, piece, captured) {
    if (move.castle === 'K') return 'O-O';
    if (move.castle === 'Q') return 'O-O-O';
    let n = '';
    const letter = PIECE_LETTER[piece] || '';
    const isCapture = captured !== EMPTY || move.ep;
    const pt = isWhite(piece) ? piece : piece - 6;
    if (pt === WP) { if (isCapture) n += String.fromCharCode(97 + move.fc); }
    else n += letter;
    if (isCapture) n += 'x';
    n += String.fromCharCode(97 + move.tc) + (8 - move.tr);
    if (move.promo) n += '=' + PIECE_LETTER[move.promo];
    return n;
  }

  function logMove(notation) {
    if (turn === 'b') {
      moveList.push({ num: fullmove - (turn === 'b' ? 0 : 1), w: notation, b: null });
    } else {
      if (moveList.length > 0) moveList[moveList.length - 1].b = notation;
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
    if (pieces.length === 2) return true;
    if (pieces.length === 3) {
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
    if (history.length === 0 || aiThinking) return;
    // Undo twice to get back to player's turn (undo AI move + player move)
    const undoCount = turn === HUMAN ? 2 : 1;
    for (let i = 0; i < undoCount && history.length > 0; i++) {
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

      if (moveList.length > 0) {
        const last = moveList[moveList.length - 1];
        if (last.b !== null) last.b = null;
        else moveList.pop();
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

    if (gameOver) {
      if (legal.length === 0 && check) {
        const winner = turn === 'w' ? 'AI' : 'You';
        statusEl.textContent = `Checkmate — ${winner} win!`;
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
      }
    } else if (aiThinking) {
      statusEl.textContent = 'AI is thinking...';
      statusEl.className = 'status';
    } else if (check) {
      statusEl.textContent = 'You are in check!';
      statusEl.className = 'status check';
    } else {
      statusEl.textContent = 'Your move';
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

        if (lastMove && ((r === lastMove.fr && c === lastMove.fc) || (r === lastMove.tr && c === lastMove.tc)))
          sq.classList.add('last-move');
        if (selected && r === selected.r && c === selected.c)
          sq.classList.add('selected');

        const isLegal = legalMoves.some(m => m.tr === r && m.tc === c);
        if (isLegal) {
          if (board[r][c] !== EMPTY || (enPassant && legalMoves.some(m => m.tr === r && m.tc === c && m.ep)))
            sq.classList.add('legal-capture');
          else sq.classList.add('legal-move');
        }

        if (check && kingPos && r === kingPos.r && c === kingPos.c)
          sq.classList.add('in-check');

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

    const sortCaptures = arr => [...arr].sort((a, b) => (PIECE_VALUE[b] || 0) - (PIECE_VALUE[a] || 0));
    whiteCapturedEl.innerHTML = sortCaptures(whiteCaptured).map(p => PIECE_UNICODE[p]).join('');
    blackCapturedEl.innerHTML = sortCaptures(blackCaptured).map(p => PIECE_UNICODE[p]).join('');
  }

  newGameBtn.addEventListener('click', init);
  undoBtn.addEventListener('click', undo);

  init();
})();

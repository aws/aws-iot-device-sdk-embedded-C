(() => {
  "use strict";

  const STORAGE_KEY = "task-manager-app:tasks:v1";

  const PRIORITY_LABEL = {
    baja: "Baja",
    media: "Media",
    alta: "Alta",
  };

  const els = {
    taskForm: document.getElementById("task-form"),
    title: document.getElementById("title"),
    description: document.getElementById("description"),
    priority: document.getElementById("priority"),
    dueDate: document.getElementById("dueDate"),
    list: document.getElementById("task-list"),
    emptyState: document.getElementById("empty-state"),
    filter: document.getElementById("filter"),
    clearDone: document.getElementById("clear-done"),
    emailForm: document.getElementById("email-form"),
    recipient: document.getElementById("recipient"),
    emailScope: document.getElementById("emailScope"),
  };

  let tasks = loadTasks();

  function loadTasks() {
    try {
      const raw = localStorage.getItem(STORAGE_KEY);
      if (!raw) return [];
      const parsed = JSON.parse(raw);
      return Array.isArray(parsed) ? parsed : [];
    } catch {
      return [];
    }
  }

  function saveTasks() {
    localStorage.setItem(STORAGE_KEY, JSON.stringify(tasks));
  }

  function makeId() {
    return Date.now().toString(36) + Math.random().toString(36).slice(2, 8);
  }

  function addTask({ title, description, priority, dueDate }) {
    tasks.unshift({
      id: makeId(),
      title: title.trim(),
      description: description.trim(),
      priority,
      dueDate: dueDate || "",
      done: false,
      createdAt: new Date().toISOString(),
    });
    saveTasks();
    render();
  }

  function toggleTask(id) {
    const t = tasks.find((x) => x.id === id);
    if (!t) return;
    t.done = !t.done;
    saveTasks();
    render();
  }

  function deleteTask(id) {
    tasks = tasks.filter((x) => x.id !== id);
    saveTasks();
    render();
  }

  function clearCompleted() {
    const remaining = tasks.filter((x) => !x.done);
    if (remaining.length === tasks.length) return;
    if (!confirm("¿Borrar todas las tareas completadas?")) return;
    tasks = remaining;
    saveTasks();
    render();
  }

  function filterTasks(scope) {
    if (scope === "pending") return tasks.filter((t) => !t.done);
    if (scope === "done") return tasks.filter((t) => t.done);
    return tasks.slice();
  }

  function formatDate(iso) {
    if (!iso) return "";
    const d = new Date(iso + "T00:00:00");
    if (Number.isNaN(d.getTime())) return iso;
    return d.toLocaleDateString(undefined, {
      year: "numeric",
      month: "short",
      day: "numeric",
    });
  }

  function render() {
    const scope = els.filter.value;
    const visible = filterTasks(scope);

    els.list.replaceChildren();

    if (visible.length === 0) {
      els.emptyState.classList.remove("hidden");
      els.emptyState.textContent =
        tasks.length === 0
          ? "No hay tareas todavía. ¡Agrega la primera!"
          : "No hay tareas en este filtro.";
      return;
    }

    els.emptyState.classList.add("hidden");

    for (const task of visible) {
      els.list.appendChild(renderTask(task));
    }
  }

  function renderTask(task) {
    const li = document.createElement("li");
    li.className = "task-item" + (task.done ? " done" : "");
    li.dataset.id = task.id;

    const checkbox = document.createElement("input");
    checkbox.type = "checkbox";
    checkbox.className = "task-checkbox";
    checkbox.checked = task.done;
    checkbox.setAttribute("aria-label", "Marcar como completada");
    checkbox.addEventListener("change", () => toggleTask(task.id));

    const body = document.createElement("div");
    body.className = "task-body";

    const title = document.createElement("p");
    title.className = "task-title";
    title.textContent = task.title;
    body.appendChild(title);

    if (task.description) {
      const desc = document.createElement("p");
      desc.className = "task-description";
      desc.textContent = task.description;
      body.appendChild(desc);
    }

    const meta = document.createElement("div");
    meta.className = "task-meta";

    const priorityTag = document.createElement("span");
    priorityTag.className = "tag priority-" + task.priority;
    priorityTag.textContent = "Prioridad: " + PRIORITY_LABEL[task.priority];
    meta.appendChild(priorityTag);

    if (task.dueDate) {
      const dateTag = document.createElement("span");
      dateTag.className = "tag";
      dateTag.textContent = "Vence: " + formatDate(task.dueDate);
      meta.appendChild(dateTag);
    }

    body.appendChild(meta);

    const actions = document.createElement("div");
    actions.className = "task-actions";

    const mailBtn = document.createElement("button");
    mailBtn.type = "button";
    mailBtn.className = "btn btn-icon";
    mailBtn.title = "Enviar esta tarea por correo";
    mailBtn.setAttribute("aria-label", "Enviar tarea por correo");
    mailBtn.textContent = "Correo";
    mailBtn.addEventListener("click", () => sendSingleTask(task));

    const delBtn = document.createElement("button");
    delBtn.type = "button";
    delBtn.className = "btn btn-icon danger";
    delBtn.title = "Eliminar tarea";
    delBtn.setAttribute("aria-label", "Eliminar tarea");
    delBtn.textContent = "Eliminar";
    delBtn.addEventListener("click", () => {
      if (confirm("¿Eliminar esta tarea?")) deleteTask(task.id);
    });

    actions.append(mailBtn, delBtn);

    li.append(checkbox, body, actions);
    return li;
  }

  function buildSummaryBody(taskList) {
    if (taskList.length === 0) return "No hay tareas para mostrar.";
    const lines = taskList.map((t, i) => {
      const status = t.done ? "[X]" : "[ ]";
      const due = t.dueDate ? " (vence " + formatDate(t.dueDate) + ")" : "";
      const prio = " - prioridad " + PRIORITY_LABEL[t.priority];
      const desc = t.description ? "\n    " + t.description.replace(/\n/g, "\n    ") : "";
      return `${i + 1}. ${status} ${t.title}${prio}${due}${desc}`;
    });
    return (
      "Resumen de tareas\n" +
      "==================\n\n" +
      lines.join("\n\n") +
      "\n\n— Generado por Gestor de Tareas"
    );
  }

  function openMailto({ to, subject, body }) {
    const url =
      "mailto:" +
      encodeURIComponent(to) +
      "?subject=" +
      encodeURIComponent(subject) +
      "&body=" +
      encodeURIComponent(body);
    window.location.href = url;
  }

  function sendSummary({ to, scope }) {
    const list = filterTasks(scope);
    if (list.length === 0) {
      alert("No hay tareas para enviar con este filtro.");
      return;
    }
    const subject =
      scope === "done"
        ? "Tareas completadas"
        : scope === "all"
        ? "Resumen de todas las tareas"
        : "Tareas pendientes";
    openMailto({ to, subject, body: buildSummaryBody(list) });
  }

  function sendSingleTask(task) {
    const to = prompt("Correo del destinatario:");
    if (!to) return;
    const trimmed = to.trim();
    if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(trimmed)) {
      alert("Correo inválido.");
      return;
    }
    const body = buildSummaryBody([task]);
    openMailto({ to: trimmed, subject: "Tarea: " + task.title, body });
  }

  els.taskForm.addEventListener("submit", (e) => {
    e.preventDefault();
    const title = els.title.value.trim();
    if (!title) return;
    addTask({
      title,
      description: els.description.value,
      priority: els.priority.value,
      dueDate: els.dueDate.value,
    });
    els.taskForm.reset();
    els.priority.value = "media";
    els.title.focus();
  });

  els.filter.addEventListener("change", render);
  els.clearDone.addEventListener("click", clearCompleted);

  els.emailForm.addEventListener("submit", (e) => {
    e.preventDefault();
    sendSummary({
      to: els.recipient.value.trim(),
      scope: els.emailScope.value,
    });
  });

  render();
})();

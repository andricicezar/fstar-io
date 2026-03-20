IMAGE_TAG ?= latest
SESSION_NAME ?= current
IMAGE_FILE ?= /tmp/image_$(IMAGE_TAG)
IMAGE_NAME ?= fstario:$(IMAGE_TAG)
CONTAINER_NAME ?= fstario_$(SESSION_NAME)

$(IMAGE_FILE):
	IMAGE_TAG=$(IMAGE_TAG) nix-build sandbox.nix -o $(IMAGE_FILE)
	docker image load -i $(IMAGE_FILE)

create_image: $(IMAGE_FILE)

delete_image:
	rm -f $(IMAGE_FILE)
	docker image rm -f $(IMAGE_NAME)

recreate_image: delete_image create_image

new_temp_session: $(IMAGE_FILE)
	docker run \
		--rm \
 		-v ~/agentstemp/claude:/home/agent/.claude \
 		-v ~/agentstemp/claude.json:/home/agent/.claude.json \
 		-v ~/agentstemp/gemini:/home/agent/.gemini \
		--env-file .env \
		-it \
		$(IMAGE_NAME) /bin/bash

new_session: $(IMAGE_FILE)
	docker run \
		--name $(CONTAINER_NAME) \
 		-v ~/agentstemp/claude:/home/agent/.claude \
 		-v ~/agentstemp/claude.json:/home/agent/.claude.json \
 		-v ~/agentstemp/gemini:/home/agent/.gemini \
		--env-file .env \
		-it $(IMAGE_NAME) \
		/bin/bash

attach_session: 
	docker attach $(CONTAINER_NAME)

load_session: 
	docker start -ai $(CONTAINER_NAME)

SYNC_FROM ?= $(shell git rev-parse HEAD)

sync_commits_from_session:
	docker exec $(CONTAINER_NAME) /bin/bash -c "cd /workspace && git format-patch $(SYNC_FROM)..HEAD --stdout" > /tmp/$(SESSION_NAME).patch
	cat /tmp/$(SESSION_NAME).patch
	git am < /tmp/$(SESSION_NAME).patch
	rm /tmp/$(SESSION_NAME).patch

delete_session:
	docker rm $(CONTAINER_NAME)
